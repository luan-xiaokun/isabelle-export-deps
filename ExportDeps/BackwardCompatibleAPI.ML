structure BackComp =
struct
  fun try_ml code =
    (ML_Context.eval_source_in NONE ML_Compiler.flags (Input.string code); true)
    handle ERROR msg => (tracing ("try_ml ERROR: " ^ msg); false)
         | Fail msg => (tracing ("try_ml Fail: " ^ msg); false)
         | Match => (tracing (""); false)

  val defined_string__nth =
    (* Isabelle2023 has String.nth *)
    try_ml "val string__nth = String.nth"
    orelse try_ml "val string__nth = fn str => fn i => String.sub (str, i)"
 

  val defined_thm_name__print_prefix =
    (* Isabelle2025 has Thm_Name.print_prefix *)
    try_ml "val thm_name__print_prefix = Thm_Name.print_prefix"
    orelse try_ml "\
\ fun thm_name__print_prefix ctxt space ((name, _)) = \
\   if name = \"\" then (Markup.empty, \"\") \
\   else (Name_Space.markup space name, Name_Space.extern ctxt space name); \
\"

  val defined_thm_name__print_suffix =
    (* Isabelle2025 has Thm_Name.print_suffix *)
    try_ml "val thm_name__print_suffix = Thm_Name.print_suffix"
    orelse try_ml "\
\ fun thm_name__print_suffix (name, index) = \
\   if name = \"\" orelse index = 0 then \"\" \
\   else enclose \"(\" \")\" (string_of_int index); \
\"

  val defined_global_theory__pretty_thm_name =
    (* Isabelle2025 has Global_Theory.pretty_thm_name *)
    try_ml "val global_theory__pretty_thm_name = Global_Theory.pretty_thm_name"
    orelse try_ml "\
\ fun global_theory__pretty_thm_name ctxt thm_name = \
\   let \
\     val facts_ = Global_Theory.facts_of (Proof_Context.theory_of ctxt) \
\     val prfx = thm_name__print_prefix ctxt (Facts.space_of facts_) thm_name; \
\     val sffx = thm_name__print_suffix thm_name; \
\   in Pretty.block [Pretty.mark_str prfx, Pretty.str sffx] end; \
\"

  val defined_thm_name__parse =
    (* Isabelle2025 has Thm_Name.parse *)
    try_ml "val thm_name__parse = Thm_Name.parse"
    orelse try_ml "\
\ fun thm_name__parse string = \
\   let \
\     val n = size string; \
\     fun char i = if 0 <= i andalso i < n then string__nth string i else #\"\\000\"; \
\     fun test pred i = pred (char i) \
\     fun is_digit c = #\"0\" <= c andalso c <= #\"9\" \
\     fun is_en c = c = #\")\" \
\     fun get_digit c = Char.ord c - Char.ord #\"0\" \
\     fun scan i k m = \
\       let val c = char i in \
\         if is_digit c then scan (i - 1) (k * 10) (m + k * get_digit c) \
\         else if c = #\"(\" then (String.substring (string, 0, i), m) \
\         else (string, 0) \
\       end; \
\   in \
\     if test is_en (n - 1) andalso test is_digit (n - 2) \
\     then scan (n - 2) 1 0 \
\     else (string, 0) \
\   end \
\"

(*
  val defined_thm__the_name_hint =
    (* Isabelle2025 has Thm.the_name_hint *)
    try_ml "\
\ fun thm__the_name_hint thm = \
\   let val thm_name = thm_name__parse (Properties.get_string (Thm.get_tags thm) Markup.nameN) \
\   in \
\     if #1 thm_name = \"\" \
\     then raise THM (\"THm.the_name_hint: missing name\", 0, [thm]) \
\     else thm_name \
\   end; \
\"
*)

  val defined_properties__get_string =
    (* Isabelle2023 has Properties.get_string *)
    try_ml "val properties__get_string = Properties.get_string"
    orelse try_ml "val properties__get_string: Properties.T -> string -> string = the_default \"\" oo (AList.lookup (op =))"

  val defined_thm_name__is_empty =
    (* Isabelle2025 has Thm_Name.is_empty *)
    try_ml "val thm_name__is_empty = Thm_Name.is_empty"
    orelse try_ml "fun thm_name__is_empty (name, _) = name = \"\""

  val defined_global_theory__lookup_thm =
    (* Isabelle2025's Global_Theory.lookup_thm returns Thm_Name.P option *)
    try_ml "val global_theory__lookup_thm: theory -> thm -> (Proofterm.thm_id * Thm_Name.P) option = Global_Theory.lookup_thm"
    orelse try_ml "\
\ fun global_theory__lookup_thm thy thm = \
\   case Global_Theory.lookup_thm thy thm of \
\     SOME (thm_id, a) => SOME (thm_id, (a, ())) \
\   | NONE => NONE \
\"

  val defined_lookup_thm_id =
    try_ml "\
\ fun lookup_thm_id thy thm_id default : (string * int) = \
\   case Global_Theory.lookup_thm_id thy thm_id of \
\     SOME (a, _) => a \
\   | NONE => default \
\" orelse try_ml "\
\ fun lookup_thm_id thy thm_id default = \
\   case Global_Theory.lookup_thm_id thy thm_id of \
\     SOME a => a \
\   | NONE => default \
\"

  val defined_proof_head_of =
    try_ml "val proof_head_of = Proofterm.proof_head_of"
    orelse try_ml "\
\ fun proof_head_of (p %% _) = proof_head_of p \
\   | proof_head_of p = p; \
\"

  val defined_term_head_of =
    try_ml "val term_head_of = Proofterm.term_head_of"
    orelse try_ml "\
\ fun term_head_of (p % _) = term_head_of p \
\   | term_head_of p = p; \
\"

  (* Extract the position of the defining command from a theorem's proof term.
     command_pos in the PThm header is set via Position.thread_data() when the
     theorem is registered, pointing to the keyword (lemma/fun/...) in source. *)
  val defined_thm_command_pos =
    try_ml "\
\   fun thm_command_pos (thm: thm) : Position.T = \
\     (case try (term_head_of o proof_head_of o Thm.proof_of) thm of \
\       SOME (Proofterm.PThm ({command_pos, ...}, _)) => command_pos \
\     | _ => Position.none) \
\"
    orelse try_ml "\
\   fun thm_command_pos (thm: thm) : Position.T = \
\     (case try (term_head_of o proof_head_of o Thm.proof_of) thm of \
\       SOME (Proofterm.PThm ({pos, ...}, _)) => hd pos \
\     | _ => Position.none) \
\"

  val defined_context__theory_name =
    try_ml "val context__theory_name: {long: bool} -> theory -> string = Context.theory_name"
    orelse try_ml "val context__theory_name: {long: bool} -> theory -> string = Context.theory_name'"

end