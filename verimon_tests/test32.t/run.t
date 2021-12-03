  $ echo 'v <- CNT x p(x,y)' > test_agg_empty_rel_1.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_1.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (3)
  @30 (time point 2): (0)

  $ echo 'v <- CNT y p(x,y)' > test_agg_empty_rel_2.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_2.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (3)
  @30 (time point 2): (0)

  $ echo 'v <- SUM y p(x,y)' > test_agg_empty_rel_3.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_3.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (6)
  @30 (time point 2): (0)

  $ echo 'v <- AVG y p(x,y)' > test_agg_empty_rel_4.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_4.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (2)
  @30 (time point 2): (0)

  $ echo 'v <- MED y p(x,y)' > test_agg_empty_rel_5.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_5.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (2)
  @30 (time point 2): (0)

  $ echo 'v <- MIN y p(x,y)' > test_agg_empty_rel_6.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_6.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (1)
  @30 (time point 2): (0)

  $ echo 'v <- MAX y p(x,y)' > test_agg_empty_rel_7.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_7.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (3)
  @30 (time point 2): (0)

  $ echo 'v <- CNT y; x p(x,y)' > test_agg_empty_rel_8.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_8.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (1,"b") (2,"a")

  $ echo 'v <- SUM y; x p(x,y)' > test_agg_empty_rel_9.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_9.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (3,"a") (3,"b")

  $ echo 'v <- AVG y; x p(x,y)' > test_agg_empty_rel_10.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_10.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (1.5,"a") (3,"b")

  $ echo 'v <- MED y; x p(x,y)' > test_agg_empty_rel_11.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_11.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (1.5,"a") (3,"b")

  $ echo 'v <- MIN y; x p(x,y)' > test_agg_empty_rel_12.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_12.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (1,"a") (3,"b")

  $ echo 'v <- MAX y; x p(x,y)' > test_agg_empty_rel_13.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_13.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (2,"a") (3,"b")

  $ echo 'v <- CNT y ONCE p(x,y)' > test_agg_empty_rel_14.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_14.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (3)
  @30 (time point 2): (3)

  $ echo 'v <- SUM y ONCE p(x,y)' > test_agg_empty_rel_15.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_15.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (6)
  @30 (time point 2): (6)

  $ echo 'v <- AVG y ONCE p(x,y)' > test_agg_empty_rel_16.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_16.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (2)
  @30 (time point 2): (2)

  $ echo 'v <- MED y ONCE p(x,y)' > test_agg_empty_rel_17.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_17.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (2)
  @30 (time point 2): (2)

  $ echo 'v <- MIN y ONCE p(x,y)' > test_agg_empty_rel_18.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_18.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (1)
  @30 (time point 2): (1)

  $ echo 'v <- MAX y ONCE p(x,y)' > test_agg_empty_rel_19.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_19.mfotl -log test_agg_empty_rel.log -nonewlastts
  @10 (time point 0): (0)
  @20 (time point 1): (3)
  @30 (time point 2): (3)

  $ echo 'v <- CNT y; x ONCE p(x,y)' > test_agg_empty_rel_20.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_20.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (1,"b") (2,"a")
  @30 (time point 2): (1,"b") (2,"a")

  $ echo 'v <- SUM y; x ONCE p(x,y)' > test_agg_empty_rel_21.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_21.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (3,"a") (3,"b")
  @30 (time point 2): (3,"a") (3,"b")

  $ echo 'v <- AVG y; x ONCE p(x,y)' > test_agg_empty_rel_22.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_22.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (1.5,"a") (3,"b")
  @30 (time point 2): (1.5,"a") (3,"b")

  $ echo 'v <- MED y; x ONCE p(x,y)' > test_agg_empty_rel_23.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_23.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (1.5,"a") (3,"b")
  @30 (time point 2): (1.5,"a") (3,"b")

  $ echo 'v <- MIN y; x ONCE p(x,y)' > test_agg_empty_rel_24.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_24.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (1,"a") (3,"b")
  @30 (time point 2): (1,"a") (3,"b")

  $ echo 'v <- MAX y; x ONCE p(x,y)' > test_agg_empty_rel_25.mfotl
  $ monpoly -verified -sig test_agg_empty_rel.sig -formula test_agg_empty_rel_25.mfotl -log test_agg_empty_rel.log -nonewlastts
  @20 (time point 1): (2,"a") (3,"b")
  @30 (time point 2): (2,"a") (3,"b")
