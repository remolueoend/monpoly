  $ echo 'LET P() = PREVIOUS FALSE IN A()' > test41_1.mfotl
  $ monpoly -verified -sig test41.sig -formula test41_1.mfotl -log test41.log -unfold_let no
  @0 (time point 1): true
