  $ echo 'ONCE[2,21) P(x)' > test11_1.mfotl
  $ monpoly -sig test11.sig -formula test11_1.mfotl -log test11.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[2,21) P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @13 (time point 0): ()
  At time point 1:
  @15 (time point 1): ((111))
  At time point 2:
  @30 (time point 2): ((111),(222))
  At time point 3:
  @31 (time point 3): ((111),(222))
  At time point 4:
  @31 (time point 4): ((111),(222))
  At time point 5:
  @31 (time point 5): ((111),(222))
  At time point 6:
  @32 (time point 6): ((111),(222))
  At time point 7:
  @32 (time point 7): ((111),(222))
  At time point 8:
  @32 (time point 8): ((111),(222))
  At time point 9:
  @32 (time point 9): ((111),(222))
  At time point 10:
  @32 (time point 10): ((111),(222))
  At time point 11:
  @32 (time point 11): ((111),(222))
  At time point 12:
  @32 (time point 12): ((111),(222))
  At time point 13:
  @33 (time point 13): ((111),(222),(333))
  At time point 14:
  @33 (time point 14): ((111),(222),(333))
  At time point 15:
  @34 (time point 15): ((222),(333),(444))
  At time point 16:
  @40 (time point 16): ((333),(444))
