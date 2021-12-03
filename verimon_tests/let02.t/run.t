  $ monpoly -verified -sig let02.sig -log let02.log -formula let02.mfotl
  @1 (time point 1): (0,10) (1,10)
  @2 (time point 2): (1,10) (2,12)
  $ monpoly -verified -sig let02.sig -log let02.log -formula let02.mfotl -unfold_let smart
  @1 (time point 1): (0,10) (1,10)
  @2 (time point 2): (1,10) (2,12)
  $ monpoly -verified -sig let02.sig -log let02.log -formula let02.mfotl -unfold_let full
  @1 (time point 1): (0,10) (1,10)
  @2 (time point 2): (1,10) (2,12)
