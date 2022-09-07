correctly resolved types in nested scopes
  $ monpoly -sig json02.sig -formula json02.mfotl -log json02.log -json_log
  @0 (time point 0): (5,"kernel")
  @10 (time point 1): (1,"driver") (5,"kernel")
  @20 (time point 2): (1,"driver") (5,"kernel")

