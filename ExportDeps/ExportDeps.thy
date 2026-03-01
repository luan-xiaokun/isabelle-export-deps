theory ExportDeps
  imports Main
  keywords "export_deps" :: diag
begin

ML \<open>
val exporter_version = "0.1.0"
structure State_Deps =
struct
  fun thy_name thy = Context.theory_name {long = true} thy

  (* Imports closure (ancestor theory names). *)
  fun theory_ancestors thy : string list =
    let
      fun step (thy: theory) (seen: string list) : string list =
        let
          val name = thy_name thy
          val seen' = insert (op =) name seen
          val parents = Theory.parents_of thy
          fun go_parent p acc =
            let val pn = thy_name p
            in if member (op =) acc pn then acc else step p acc end
        in
          fold go_parent parents seen'
        end
    in
      rev (step thy [])
    end
    handle ERROR _ => [thy_name thy]
         | Fail _ => [thy_name thy]
         | Match => [thy_name thy]

  fun term_const_names t = sort_strings (Term.add_const_names t [])

  fun term_type_names t : string list =
    let
      fun addT (Type (name, Ts)) acc = fold addT Ts (insert (op =) name acc)
        | addT (TFree _) acc = acc
        | addT (TVar _) acc = acc
    in
      sort_strings (Term.fold_types addT t [])
    end
    handle ERROR _ => []
         | Fail _ => []
         | Match => []

  fun plain_term ctxt t =
    Print_Mode.setmp [] (fn () =>
      let
        val ctxt' = Config.put Printer.show_types true ctxt
      in
        Pretty.unformatted_string_of (Syntax.pretty_term ctxt' t)
      end) ()

  fun sha1_text s = SHA1.rep (SHA1.digest s)

  fun isabelle_identifier () =
    Isabelle_System.isabelle_identifier () |> the_default "Unknown"

  (* ---------- TOML helpers ---------- *)

  fun toml_escape s =
    String.translate
      (fn #"\"" => "\\\""
        | #"\\" => "\\\\"
        | #"\n" => "\\n"
        | #"\t" => "\\t"
        | #"\r" => "\\r"
        | c => String.str c) s

  fun toml_string s = "\"" ^ toml_escape s ^ "\""

  fun toml_bool b = if b then "true" else "false"

  fun toml_string_array xs =
    "[" ^ String.concatWith ", " (map toml_string xs) ^ "]"

  (* ---------- Common theorem naming / identity helpers ---------- *)

  fun key_of (thy_name: string) ((name, sel): Thm_Name.T) : string =
    thy_name ^ ":" ^ name ^ (if sel = 0 then "" else "#" ^ Int.toString sel)

  fun thm_id_to_string thm_id =
    #theory_name thm_id ^ "#" ^ Int.toString (#serial thm_id)

  fun pos_to_string (pos: Position.T) : string =
    let
      fun opt_int NONE = "-" | opt_int (SOME i) = Int.toString i
      fun opt_str NONE = "-" | opt_str (SOME s) = s

      val file = opt_str (Position.file_of pos)
      val line = opt_int (Position.line_of pos)
      val off  = opt_int (Position.offset_of pos)
      val eoff = opt_int (Position.end_offset_of pos)
    in
      file ^ ":" ^ line ^ ":" ^ off ^ ":" ^ eoff
    end

  fun pretty_name ctxt (a: Thm_Name.T) : string =
    Print_Mode.setmp [] (fn () =>
      Pretty.unformatted_string_of (Global_Theory.pretty_thm_name ctxt a)) ()

  fun fallback_name thy thm : Thm_Name.T * string * string * string * string =
    let
      val a = Thm.get_name_hint thm
      val thy_n = thy_name thy
    in
      if Thm_Name.is_empty a then
        let
          val raw = "<anonymous>"
          val sel = 0
          val pretty = "<anonymous>"
          val key = thy_n ^ ":" ^ raw
        in
          ((raw, sel), key, pretty, thy_n, "<none>")
        end
      else
        let
          val pretty = Thm_Name.print a
          val key = key_of thy_n a
        in
          (a, key, pretty, thy_n, "<none>")
        end
    end

  (* ---------- Structured records ---------- *)

  datatype dep_rec =
    Dep of {
      key: string,
      raw: string,
      sel: int,
      pretty: string,
      theory: string,
      thm_id: string,
      fingerprint: string,
      pos: string
    }

  datatype thm_rec =
    Thm_Rec of {
      key: string,
      raw: string,
      sel: int,
      pretty: string,
      theory: string,
      thm_id: string,
      fingerprint: string,
      proposition: string,
      constants: string list,
      types: string list,
      has_skip_proof: bool,
      pos: string,
      dependencies: dep_rec list
    }

  (* ---------- Dependency collection for one theorem ---------- *)

  fun dep_fingerprint ctxt thy (a: Thm_Name.T) =
    (case try (fn x => Global_Theory.get_thm_name thy x) (a, Position.none) of
      SOME dep_thm => sha1_text (plain_term ctxt (Thm.prop_of dep_thm))
    | NONE => "")

  fun collect_dep_rec ctxt thy (thm_id, a: Thm_Name.T) =
    let
      val thy_n = #theory_name thm_id
      val (a', pos) =
        (case Global_Theory.lookup_thm_id thy thm_id of
          SOME pair => pair
        | NONE => (a, Position.none))
      val (raw, sel) = a'
      val pretty = pretty_name ctxt a'
      val key = key_of thy_n a'
      val fp = dep_fingerprint ctxt thy a'
      val thm_id_s = thm_id_to_string thm_id
      val pos_s = pos_to_string pos
    in
      Dep {
        key = key,
        raw = raw,
        sel = sel,
        pretty = pretty,
        theory = thy_n,
        thm_id = thm_id_s,
        fingerprint = fp,
        pos = pos_s
      }
    end

  fun thm_deps_records ctxt (thm: thm) : dep_rec list =
    let
      val thy = Proof_Context.theory_of ctxt
      val deps =
        (case try (Thm_Deps.thm_deps thy) [thm] of
          SOME ds => ds
        | NONE => [])
      val recs = map (collect_dep_rec ctxt thy) deps
      fun key_of_dep (Dep {key, ...}) = key
    in
      sort_by key_of_dep recs
    end

  (* ---------- Theorem collection ---------- *)

  fun collect_thm_rec ctxt (thm: thm) : thm_rec =
    let
      val thy = Proof_Context.theory_of ctxt
      val t = Thm.prop_of thm
      val prop_txt = plain_term ctxt t
      val cs = term_const_names t
      val ts = term_type_names t
      val has_skip = Thm_Deps.has_skip_proof [thm]
      val fp = sha1_text prop_txt

      val ((raw, sel), key, pretty, theory, thm_id_s, pos_s) =
        (case Global_Theory.lookup_thm thy thm of
          SOME (thm_id, (a, pos)) =>
            let
              val thy_n = #theory_name thm_id
            in
              (a,
               key_of thy_n a,
               pretty_name ctxt a,
               thy_n,
               thm_id_to_string thm_id,
               pos_to_string pos)
            end
        | NONE =>
            let
              val (a, key, pretty, theory, thm_id_s) = fallback_name thy thm
            in
              (a, key, pretty, theory, thm_id_s, pos_to_string Position.none)
            end)

      val deps = thm_deps_records ctxt thm
    in
      Thm_Rec {
        key = key,
        raw = raw,
        sel = sel,
        pretty = pretty,
        theory = theory,
        thm_id = thm_id_s,
        fingerprint = fp,
        proposition = prop_txt,
        constants = cs,
        types = ts,
        has_skip_proof = has_skip,
        pos = pos_s,
        dependencies = deps
      }
    end

  (* ---------- TOML rendering ---------- *)

  fun render_dep_toml
    (Dep {key, raw, sel, pretty, theory, thm_id, fingerprint, pos}) =
    String.concat [
      "[[theorems.dependencies]]\n",
      "key = ", toml_string key, "\n",
      "raw = ", toml_string raw, "\n",
      "sel = ", Int.toString sel, "\n",
      "pretty = ", toml_string pretty, "\n",
      "theory = ", toml_string theory, "\n",
      "thm_id = ", toml_string thm_id, "\n",
      "fingerprint = ", toml_string fingerprint, "\n",
      "pos = ", toml_string pos, "\n",
      "\n"
    ]

  fun render_thm_toml
    (Thm_Rec {key, raw, sel, pretty, theory, thm_id, fingerprint,
              proposition, constants, types, has_skip_proof, pos, dependencies}) =
    String.concat (
      [
        "[[theorems]]\n",
        "key = ", toml_string key, "\n",
        "raw = ", toml_string raw, "\n",
        "sel = ", Int.toString sel, "\n",
        "pretty = ", toml_string pretty, "\n",
        "theory = ", toml_string theory, "\n",
        "thm_id = ", toml_string thm_id, "\n",
        "fingerprint = ", toml_string fingerprint, "\n",
        "proposition = ", toml_string proposition, "\n",
        "constants = ", toml_string_array constants, "\n",
        "types = ", toml_string_array types, "\n",
        "has_skip_proof = ", toml_bool has_skip_proof, "\n",
        "pos = ", toml_string pos, "\n",
        "\n"
      ] @ map render_dep_toml dependencies
    )

  fun report_thms ctxt (thms: thm list) =
    let
      val thy = Proof_Context.theory_of ctxt
      val thm_recs = map (collect_thm_rec ctxt) thms
      val ancestors = theory_ancestors thy
    in
      String.concat (
        [
          "[meta]\n",
          "current_theory = ", toml_string (thy_name thy), "\n",
          "theory_ancestors = ", toml_string_array ancestors, "\n",
          "exporter_version = ", toml_string exporter_version, "\n",
          "isabelle_identifier = ", toml_string (isabelle_identifier ()), "\n",
          "\n"
        ] @ map render_thm_toml thm_recs
      )
    end
end
\<close>

ML \<open>
local
  val parse_to: string option parser =
    Scan.option (Parse.$$$ "in" |-- Parse.path)
in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>export_deps\<close>
    "export dependency snapshot of finished theorems/facts to a file"
    (Parse.thms1 -- parse_to
      >> (fn (facts, file_opt) =>
        Toplevel.keep (fn st =>
          let
            val ctxt = Toplevel.context_of st
            val thms = Attrib.eval_thms ctxt facts

            val thy = Proof_Context.theory_of ctxt
            val base_dir = Resources.master_directory thy
            val path =
              (case file_opt of
                NONE => Path.basic "deps.toml"
              | SOME s => Path.explode s)
            val full_path = Path.append base_dir path
            val txt = State_Deps.report_thms ctxt thms
          in
            File.write full_path txt
          end)))
end
\<close>

end