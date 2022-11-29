import Lake
open Lake DSL

package proj {
  -- add package configuration options here
}

lean_lib Proj {
  -- add library configuration options here
}

@[default_target]
lean_exe proj {
  root := `Main
}

require std from git "https://github.com/leanprover/std4" @ "main"
