theory ExportDeps
  imports Pure
  keywords "export_deps" :: diag
begin

ML_file "BackwardCompatibleAPI.ML"

ML_file "ExportDeps.ML"

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
            val thms =
              (Attrib.eval_thms ctxt facts
               handle ERROR msg => error ("export_deps: " ^ msg))

            val thy = Proof_Context.theory_of ctxt
            val base_dir = Resources.master_directory thy
            val path =
              (case file_opt of
                NONE => Path.basic "deps.toml"
              | SOME s => Path.explode s)
            val full_path = Path.append base_dir path

          in
            (State_Deps.write_thms_to_path full_path ctxt thms
             handle ERROR msg => error ("export_deps: error collecting theorem data: " ^ msg)
                  | IO.Io {name, ...} => error ("export_deps: cannot write output file: " ^ name))
          end)))
end
\<close>

end
