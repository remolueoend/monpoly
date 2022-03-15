Type inference must begin with distinct type variables

  $ echo 'LET Q() = EXISTS x. P(x) IN Q() AND z <- AVG y y = 42' > type07_1.mfotl
  $ monpoly -sig type07.sig -log type07.log -formula type07_1.mfotl
  @0 (time point 0): (42)
