  $ rm -rf test39.sta > /dev/null
  $ echo 'ONCE[0,0] P(x)' > test39_1.mfotl
  $ monpoly -sig test39.sig -formula test39_1.mfotl -log test39_a.log -nonewlastts
  Saved state
  $ monpoly -sig test39.sig -formula test39_1.mfotl -log test39_b.log -nonewlastts -load test39.sta
  Loaded state
  @3 (time point 3): ("foo")

  $ rm -rf test39.sta > /dev/null
  $ echo 'ONCE[1,1] P(x)' > test39_2.mfotl
  $ monpoly -sig test39.sig -formula test39_2.mfotl -log test39_a.log -nonewlastts
  Saved state
  $ monpoly -sig test39.sig -formula test39_2.mfotl -log test39_b.log -nonewlastts -load test39.sta
  Loaded state
  @4 (time point 4): ("foo")

  $ rm -rf test39.sta > /dev/null
  $ echo 'EVENTUALLY[0,0] P(x)' > test39_3.mfotl
  $ monpoly -sig test39.sig -formula test39_3.mfotl -log test39_a.log -nonewlastts
  Saved state
  $ monpoly -sig test39.sig -formula test39_3.mfotl -log test39_b.log -nonewlastts -load test39.sta
  Loaded state
  @3 (time point 3): ("foo")

  $ rm -rf test39.sta > /dev/null
  $ echo 'EVENTUALLY[1,1] P(x)' > test39_4.mfotl
  $ monpoly -sig test39.sig -formula test39_4.mfotl -log test39_a.log -nonewlastts
  Saved state
  $ monpoly -sig test39.sig -formula test39_4.mfotl -log test39_b.log -nonewlastts -load test39.sta
  Loaded state
  @2 (time point 2): ("foo")

