theory ExportDeps
  imports Main
  keywords "export_deps" :: diag
begin

ML \<open>
structure State_Deps =
struct
  fun thy_name thy = Context.theory_name {long = true} thy
  val x = Theory.ancestors_of
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

  (* Local named facts in scope. *)
  fun local_fact_names ctxt : string list =
    (Proof_Context.facts_of ctxt
      |> Facts.dest_static false []
      |> map fst
      |> sort_strings)
    handle ERROR _ => []
         | Fail _ => []
         | Match => []

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
      end) ();

  fun show_list title xs =
    if null xs then title ^ " (none)\n"
    else title ^ " (" ^ Int.toString (length xs) ^ "):\n  "
      ^ String.concatWith "\n  " xs ^ "\n"

  (* ---------- Structured deps (key/raw/sel/pretty/theory/pos) ---------- *)
  
  datatype dep_rec =
    Dep of {
      key: string,           (* canonical ID for DB join *)
      raw_name: string,      (* internal fact name: fst Thm_Name.T *)
      sel: int,              (* selection index: snd Thm_Name.T *)
      pretty: string,        (* display name in current ctxt *)
      theory: string,        (* theory name from thm_id *)
      pos: Position.T        (* definition position from Global_Theory.lookup_thm_id *)
    };
  
  fun key_of (thy_name: string) ((name, sel): Thm_Name.T) : string =
    (* Canonical ID: include theory_name from thm_id to avoid any remaining ambiguity.
       Use #sel only for multi-facts (sel>0). *)
    thy_name ^ ":" ^ name ^ (if sel = 0 then "" else "#" ^ Int.toString sel);
  
  fun pos_to_string (pos: Position.T) : string =
    let
      fun opt_int NONE = "-" | opt_int (SOME i) = Int.toString i;
      fun opt_str NONE = "-" | opt_str (SOME s) = s;
  
      val file = opt_str (Position.file_of pos);
      val line = opt_int (Position.line_of pos);
      val off  = opt_int (Position.offset_of pos);
      val eoff = opt_int (Position.end_offset_of pos);
    in
      file ^ ":" ^ line ^ ":" ^ off ^ ":" ^ eoff
    end;
  
  fun pretty_name ctxt (a: Thm_Name.T) : string =
    Print_Mode.setmp [] (fn () =>
      Pretty.unformatted_string_of (Global_Theory.pretty_thm_name ctxt a)) ();
  
  fun dep_rec_to_lines (Dep {key, raw_name, sel, pretty, theory, pos}) : string =
    String.concat
      [ "- key: ", key, "\n",
        "  raw: ", raw_name, "\n",
        "  sel: ", Int.toString sel, "\n",
        "  pretty: ", pretty, "\n",
        "  theory: ", theory, "\n",
        "  pos: ", pos_to_string pos, "\n"
      ];
  
  fun thm_deps_records ctxt (thms: thm list) : dep_rec list =
    let
      val thy = Proof_Context.theory_of ctxt
      val deps =
        (case try (Thm_Deps.thm_deps thy) thms of
           SOME ds => ds
         | NONE => [])
  
      fun mk (thm_id, a: Thm_Name.T) =
        (case Global_Theory.lookup_thm_id thy thm_id of
           NONE =>
             (* Should be rare: thm_id not in global mapping. We still emit a record
                with Position.none to keep the export total. *)
             let
               val thy_name = #theory_name thm_id
               val (name, sel) = a
             in
               Dep { key = key_of thy_name a,
                     raw_name = name,
                     sel = sel,
                     pretty = pretty_name ctxt a,
                     theory = thy_name,
                     pos = Position.none }
             end
         | SOME (a', pos) =>
             let
               val thy_name = #theory_name thm_id
               val (name, sel) = a'
             in
               Dep { key = key_of thy_name a',
                     raw_name = name,
                     sel = sel,
                     pretty = pretty_name ctxt a',
                     theory = thy_name,
                     pos = pos }
             end)
  
      val recs = map mk deps
      fun key (Dep {key, ...}) = key
    in
      sort_by key recs
    end;
  
  fun show_deps_block ctxt (thms: thm list) : string =
    let
      val recs = thm_deps_records ctxt thms
      val header =
        "Theorem dependencies (thm_deps) (" ^ Int.toString (length recs) ^ "):\n"
    in
      header ^ String.concat (map dep_rec_to_lines recs) ^ "\n"
    end;

  fun show_one_thm ctxt (thm: thm) =
    let
      val t = Thm.prop_of thm
      val cs = term_const_names t
      val ts = term_type_names t
      val nm = Thm.get_name_hint thm
      val prop_txt = plain_term ctxt t
      val fp = SHA1.rep (SHA1.digest prop_txt)
    in
      "Theorem: " ^ (if Thm_Name.is_empty nm then "<anonymous>" else Thm_Name.print nm) ^ "\n"
      ^ "  fingerprint: " ^ fp ^ "\n"
      ^ "  proposition: " ^ prop_txt ^ "\n"
      ^ show_list "  constants" cs
      ^ show_list "  types" ts
    end

  fun report_thms ctxt (thms: thm list) =
    let
      val thy = Proof_Context.theory_of ctxt
      val ancestors = theory_ancestors thy
      val has_skip = Thm_Deps.has_skip_proof thms
  
      val header =
        "=== THEOREM DEPENDENCIES SNAPSHOT ===\n"
        ^ "Current theory: " ^ thy_name thy ^ "\n"
        ^ show_list "Theory ancestors (imports closure)" ancestors
        ^ "\n"
  
      val dep_block = show_deps_block ctxt thms

      val has_skip_block = "Has skip proof: " ^ (if has_skip then "true" else "false") ^ "\n\n"
    in
      header
      ^ dep_block
      ^ has_skip_block
      ^ String.concat (map (fn th => show_one_thm ctxt th ^ "\n") thms)
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
                 NONE => Path.basic "deps.txt"
               | SOME s => Path.explode s)
            val full_path = Path.append base_dir path
            val txt = State_Deps.report_thms ctxt thms
          in
            File.write full_path txt
          end)))
end
\<close>

end
