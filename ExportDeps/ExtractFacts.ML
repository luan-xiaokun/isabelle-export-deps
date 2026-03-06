(*  ExtractFacts.ML — Extract_Facts structure + extract_facts/extract_deps commands.
    Loaded via ML_file from ExtractFacts.thy (HOL workflow) and from
    flat ZF/FOL wrapper theories (object-logic-agnostic workflow).

    Requires the following keywords to be declared in the loading theory header:
      keywords "extract_facts" :: diag and "extract_deps" :: diag  *)

structure Extract_Facts =
struct

  (* ---------- command / fact records ---------- *)

  datatype fact_rec =
    Fact_Rec of {
      name: string,
      command: string,
      fact_names: string list,
      text: string
    }

  (* ---------- parse text into transitions + source slices ---------- *)

  fun parse_outer_syntax thy source : (Toplevel.transition * string) list =
    let
      val transitions = Outer_Syntax.parse_text thy (K thy) Position.start source

      fun addtext symbols [tr] = [(tr, implode symbols)]
        | addtext _ [] = []
        | addtext symbols (tr :: next_tr :: trs) =
            let
              val dist =
                Position.distance_of (Toplevel.pos_of tr, Toplevel.pos_of next_tr)
                |> the
              val (this, rest) = chop dist symbols
            in
              (tr, implode this) :: addtext rest (next_tr :: trs)
            end
    in
      addtext (Symbol.explode source) transitions
    end

  (* ---------- supported commands ---------- *)

  fun supported_command cmd =
    member (op =) [
      "theorem", "lemma", "corollary", "proposition", "schematic_goal",
      "lemmas", "definition",
      "fun", "primrec", "inductive", "datatype",
      "axiomatization",
      "nominal_datatype", "nominal_primrec", "nominal_inductive"
    ] cmd

  (* ---------- name extraction helpers ---------- *)

  fun drop_leading_ws s =
    let
      fun p [] = []
        | p (c :: cs) = if Symbol.is_blank c then p cs else c :: cs
    in
      implode (p (Symbol.explode s))
    end

  fun take_ident_prefix s =
    let
      fun ok c =
        Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"'"
      fun go [] acc = String.implode (rev acc)
        | go (c :: cs) acc = if ok c then go cs (c :: acc) else String.implode (rev acc)
    in
      go (String.explode s) []
    end

  fun strip_command_prefix cmd text =
    let
      val t = drop_leading_ws text
      val cmd_len = size cmd
    in
      if String.isPrefix cmd t then
        String.extract (t, cmd_len, NONE) |> drop_leading_ws
      else t
    end

  (* For "datatype ('a, 'b) t = ...", extract "t" by scanning past type params. *)
  fun extract_datatype_name cmd text : string option =
    let
      val rest = strip_command_prefix cmd text
      val lhs = case String.fields (fn c => c = #"=") rest of
        (s :: _) => s
        | [] => rest
      val toks = String.tokens
        (fn c => Char.isSpace c orelse c = #"(" orelse c = #")" orelse c = #",")
        lhs
    in
      List.find (fn t => t <> "" andalso Char.isAlpha (String.sub (t, 0))) toks
    end

  fun extract_name cmd text : string option =
    if cmd = "datatype" orelse cmd = "nominal_datatype" then
      extract_datatype_name cmd text
    else
      let
        val rest = strip_command_prefix cmd text
        val name = take_ident_prefix rest
      in
        if name = "" then NONE else SOME name
      end

  (* ---------- axiom name scanner (for "axiomatization") ---------- *)

  (* Scan past a double-quoted string; called after the opening '"' is consumed. *)
  fun skip_dquote [] = []
    | skip_dquote (s :: rest) =
        if s = "\\" then (case rest of _ :: r => skip_dquote r | [] => [])
        else if s = "\"" then rest
        else skip_dquote rest

  (* Skip past a cartouche (open/close symbols); called after the opening symbol is consumed.
     Nesting is tracked by depth n; double-quoted strings inside are also skipped. *)
  fun skip_cartouche 0 ss = ss
    | skip_cartouche _ [] = []
    | skip_cartouche n (s :: rest) =
        if s = Symbol.open_ then skip_cartouche (n + 1) rest
        else if s = Symbol.close then skip_cartouche (n - 1) rest
        else if s = "\"" then skip_cartouche n (skip_dquote rest)
        else skip_cartouche n rest

  (* Skip past balanced []-brackets; called after the '[' is consumed.
     Nested brackets, double-quoted strings, and cartouches inside are all handled. *)
  fun skip_bracket 0 ss = ss
    | skip_bracket _ [] = []
    | skip_bracket n (s :: rest) =
        if s = "\"" then skip_bracket n (skip_dquote rest)
        else if s = Symbol.open_ then skip_bracket n (skip_cartouche 1 rest)
        else if s = "[" then skip_bracket (n + 1) rest
        else if s = "]" then skip_bracket (n - 1) rest
        else skip_bracket n rest

  fun is_ident_char s =
    size s = 1 andalso
    (let val c = String.sub (s, 0)
     in Char.isAlphaNum c orelse c = #"_" orelse c = #"'" end)

  fun is_ident_start s =
    size s = 1 andalso
    (let val c = String.sub (s, 0) in Char.isAlpha c orelse c = #"_" end)

  fun skip_ws [] = []
    | skip_ws (s :: rest) =
        if size s = 1 andalso Char.isSpace (String.sub (s, 0)) then skip_ws rest else s :: rest

  fun span_ident [] = ([], [])
    | span_ident (x :: xs) =
        if is_ident_char x
        then let val (ys, zs) = span_ident xs in (x :: ys, zs) end
        else ([], x :: xs)

  (* Collect "name:" and "name [attrs]:" patterns.  Both double-quoted strings and
     cartouches \<open>...\<close> are skipped so propositions don't yield false-positive names. *)
  fun collect_axiom_names [] acc = rev acc
    | collect_axiom_names (s :: rest) acc =
        if s = "\"" then
          collect_axiom_names (skip_dquote rest) acc
        else if s = Symbol.open_ then
          collect_axiom_names (skip_cartouche 1 rest) acc
        else if is_ident_start s then
          let
            val (ident_syms, after) = span_ident (s :: rest)
            val name = String.concat ident_syms
            val after' = skip_ws after
          in
            case after' of
              [] => rev acc
            | (c :: rest') =>
                if c = ":" then
                  collect_axiom_names rest' (name :: acc)
                else if c = "[" then
                  (case skip_ws (skip_bracket 1 rest') of
                     ":" :: rest'' => collect_axiom_names rest'' (name :: acc)
                   | ss => collect_axiom_names ss acc)
                else
                  collect_axiom_names after' acc
          end
        else collect_axiom_names rest acc

  (* Find "where" keyword (as a whole word), then collect axiom names after it. *)
  fun axiom_names_from_source text =
    let
      val syms = Symbol.explode text
      val where_key = ["w", "h", "e", "r", "e"]

      fun at_where ss =
        length ss >= 5 andalso
        List.take (ss, 5) = where_key andalso
        (length ss = 5 orelse not (is_ident_char (List.nth (ss, 5))))

      fun scan [] = []
        | scan (ss as (s :: rest)) =
            if s = "\"" then scan (skip_dquote rest)
            else if s = Symbol.open_ then scan (skip_cartouche 1 rest)
            else if at_where ss then collect_axiom_names (List.drop (ss, 5)) []
            else scan rest
    in
      scan syms
    end

  (* ---------- candidate fact names by command ---------- *)

  fun candidate_fact_names cmd name =
    let val s = fn sfx => name ^ sfx in
      case cmd of
        "theorem"        => [name]
      | "lemma"          => [name]
      | "corollary"      => [name]
      | "proposition"    => [name]
      | "schematic_goal" => [name]
      | "lemmas"         => [name]
      | "definition"     => [name, s "_def"]
      | "fun"            =>
          [s ".simps", s ".induct", s ".elims",
           s ".cases",
           s ".psimps", s ".pinduct", s ".pelims",
           s ".domintros"]
      | "primrec"        => [s ".simps", s ".induct"]
      | "inductive"      =>
          [s ".intros", s ".cases", s ".induct", s ".inducts", s ".simps"]
      | "datatype"       =>
          [s ".inject", s ".distinct", s ".exhaust", s ".nchotomy",
           s ".case", s ".disc", s ".discI", s ".sel",
           s ".split", s ".split_asm",
           s ".induct", s ".rec", s ".map", s ".rel",
           s ".rel_induct", s ".set",
           s ".set_cases", s ".set_intros", s ".set_induct",
           s ".map_disc_iff", s ".map_sel"]
      | "nominal_datatype" =>
          [s ".inject", s ".distinct", s ".exhaust", s ".nchotomy",
           s ".case", s ".disc", s ".discI", s ".sel",
           s ".split", s ".split_asm",
           s ".induct", s ".rec", s ".map", s ".rel",
           s ".rel_induct", s ".set",
           s ".set_cases", s ".set_intros", s ".set_induct",
           s ".map_disc_iff", s ".map_sel"]
      | "nominal_primrec"   => [s ".simps", s ".induct"]
      | "nominal_inductive" =>
          [s ".intros", s ".cases", s ".induct", s ".inducts", s ".simps"]
      | "axiomatization" => []   (* handled separately via axiom_names_from_source *)
      | _                => []
    end

  (* ---------- validate candidates against global facts ---------- *)

  fun fact_exists ctxt name =
    let val thy = Proof_Context.theory_of ctxt
    in can (Global_Theory.get_thms thy) name end

  fun existing_fact_names ctxt names =
    names |> distinct (op =) |> filter (fact_exists ctxt)

  (* ---------- collect facts from source + current theory ctxt ---------- *)

  fun collect_fact_recs ctxt source_text : fact_rec list =
    let
      val thy = Proof_Context.theory_of ctxt
      val trs = parse_outer_syntax thy source_text

      fun one (tr, text) =
        let
          val cmd = Toplevel.name_of tr
        in
          if not (supported_command cmd) then NONE
          else if cmd = "axiomatization" then
            (* Fact names come from the explicit "name: prop" labels in the where
               clause, not from name suffixes. *)
            let
              val axiom_names = axiom_names_from_source text
              val fact_names  = filter (fact_exists ctxt) axiom_names
              (* Display name: first declared constant (ident before "where"),
                 falling back to the first axiom label. *)
              val display_name =
                let val n = take_ident_prefix (strip_command_prefix cmd text)
                in if n = "" orelse n = "where" then
                     case fact_names of (n1 :: _) => n1 | [] => "<axiomatization>"
                   else n
                end
            in
              if null fact_names then NONE
              else SOME (Fact_Rec {
                name = display_name,
                command = cmd,
                fact_names = fact_names,
                text = text
              })
            end
          else
            (case extract_name cmd text of
              NONE => NONE
            | SOME name =>
                let
                  val named_candidates =
                    if member (op =) ["fun", "primrec", "inductive",
                                      "nominal_primrec", "nominal_inductive"] cmd
                    then axiom_names_from_source text |> map (fn lbl => name ^ "." ^ lbl)
                    else []
                  val fact_names =
                    (candidate_fact_names cmd name @ named_candidates)
                    |> existing_fact_names ctxt
                in
                  SOME (Fact_Rec {
                    name = name,
                    command = cmd,
                    fact_names = fact_names,
                    text = text
                  })
                end)
        end
    in
      map_filter one trs
    end

  (* ---------- TOML rendering ---------- *)

  fun render_fact_toml
    (Fact_Rec {name, command, fact_names, text}) =
    String.concat [
      "[[facts]]\n",
      "name = ", State_Deps.toml_string name, "\n",
      "command = ", State_Deps.toml_string command, "\n",
      "fact_names = ", State_Deps.toml_string_array fact_names, "\n",
      "text = ", State_Deps.toml_string text, "\n",
      "\n"
    ]

  fun report_facts ctxt source_text =
    let
      val thy = Proof_Context.theory_of ctxt
      val recs = collect_fact_recs ctxt source_text
    in
      String.concat (
        [
          "[meta]\n",
          "current_theory = ", State_Deps.toml_string (State_Deps.thy_name thy), "\n",
          "exporter_version = ", State_Deps.toml_string State_Deps.exporter_version, "\n",
          "isabelle_identifier = ", State_Deps.toml_string (State_Deps.isabelle_identifier ()), "\n",
          "\n"
        ] @ map render_fact_toml recs
      )
    end

  (* Stream fact TOML incrementally to an open outstream. *)
  fun write_facts_stream (os: TextIO.outstream) ctxt source_text =
    let
      val thy = Proof_Context.theory_of ctxt
      val recs = collect_fact_recs ctxt source_text
      fun out s = TextIO.output (os, s)
    in
      app out [
        "[meta]\n",
        "current_theory = ", State_Deps.toml_string (State_Deps.thy_name thy), "\n",
        "exporter_version = ", State_Deps.toml_string State_Deps.exporter_version, "\n",
        "isabelle_identifier = ", State_Deps.toml_string (State_Deps.isabelle_identifier ()), "\n",
        "\n"
      ];
      app (fn r => out (render_fact_toml r)) recs
    end

  (* Write fact TOML to a file path, streaming (no monolithic string). *)
  fun write_facts_to_path path ctxt source_text =
    let
      val os = TextIO.openOut (File.platform_path path)
      val result = Exn.capture (fn () => write_facts_stream os ctxt source_text) ()
      val _ =
        case result of
          Exn.Exn _ => (TextIO.closeOut os handle IO.Io _ => ())
        | Exn.Res _ => TextIO.closeOut os
    in
      Exn.release result
    end

end


(* ---------- Isar commands ----------
   Requires keywords "extract_facts" :: diag and "extract_deps" :: diag
   to be declared in the loading theory header.                          *)

local
  val parse_to: string option parser =
    Scan.option (Parse.$$$ "in" |-- Parse.path)
in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>extract_facts\<close>
    "extract supported facts from target theory source and write them to a TOML file"
    (Parse.path -- parse_to
      >> (fn (src_file, file_opt) =>
        Toplevel.keep (fn st =>
          let
            val ctxt = Toplevel.context_of st
            val thy = Proof_Context.theory_of ctxt
            val base_dir = Resources.master_directory thy

            val src_path = Path.explode src_file
            val source_text =
              (File.read src_path
               handle IO.Io {name, ...} =>
                 error ("extract_facts: cannot read source file: " ^ name))

            val out_path =
              (case file_opt of
                NONE => Path.basic "facts.toml"
              | SOME s => Path.explode s)
            val full_out_path = Path.append base_dir out_path
          in
            (Extract_Facts.write_facts_to_path full_out_path ctxt source_text
             handle ERROR msg => error ("extract_facts: " ^ msg)
                  | IO.Io {name, ...} => error ("extract_facts: cannot write output file: " ^ name))
          end)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>extract_deps\<close>
    "extract dependencies of all facts in a theory source and write them to a TOML file"
    (Parse.path -- parse_to
      >> (fn (src_file, file_opt) =>
        Toplevel.keep (fn st =>
          let
            val ctxt = Toplevel.context_of st
            val thy = Proof_Context.theory_of ctxt
            val base_dir = Resources.master_directory thy

            val src_path = Path.explode src_file
            val source_text =
              (File.read src_path
               handle IO.Io {name, ...} =>
                 error ("extract_deps: cannot read source file: " ^ name))

            val recs = Extract_Facts.collect_fact_recs ctxt source_text
            val all_fact_names =
              maps (fn Extract_Facts.Fact_Rec {fact_names, ...} => fact_names) recs
              |> distinct (op =)

            val thms =
              maps (fn n =>
                (Global_Theory.get_thms thy n
                 handle ERROR _ => [])) all_fact_names

            val out_path =
              (case file_opt of
                NONE => Path.basic "deps.toml"
              | SOME s => Path.explode s)
            val full_out_path = Path.append base_dir out_path

          in
            (State_Deps.write_thms_to_path full_out_path ctxt thms
             handle ERROR msg => error ("extract_deps: " ^ msg)
                  | IO.Io {name, ...} => error ("extract_deps: cannot write output file: " ^ name))
          end)))

end
