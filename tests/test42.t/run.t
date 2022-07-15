  $ echo 'ONCE[0,*) A()' > test42.mfotl
  $ monpoly -sig test42.sig -formula test42.mfotl -log test42.log -verified -no_rw
  @0 (time point 0): true
  $ monpoly -sig test42.sig -formula test42.mfotl -log test42.log -verified
  @0 (time point 0): true
