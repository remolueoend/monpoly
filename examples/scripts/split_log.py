from argparse import ArgumentParser

parser = ArgumentParser()
parser.add_argument("-i", "--input", help="LOGFILE to split")
parser.add_argument("-o", "--output", help="output file prefix")
parser.add_argument("-p", "--policy", help="according to which policy should the file be split")
parser.add_argument("-d", "--duplicates", help="should some elements appear in both log files?")

args = parser.parse_args()

duplicates = args.duplicates.lower() == "true"

print ("Duplicates for combine: " + str(duplicates))

def extractTs(line):
  arr = line.split(" ")
  return arr[0]

def extractVal(line, index):
  arr = line.split(" ")
  if len(arr) < 3:
    return 0

  length = len(arr[2])
  if length > 2:
    val = arr[2][1:length-2].split(",")[index]
    return int(val)
  else:
    return 0

def checkCondP1(line, o1, o2):
  if "publish" not in line and not "approve" in line:
    o1.write(line)
    o2.write(line)
  else:
    ts = extractTs(line)
    if "publish" in line:
      val = extractVal(line, 1)
    else:
      val = extractVal(line, 1)
    if duplicates and val % 3 == 0:
      o1.write(line)
      o2.write(line)
    else:
      if val % 2 == 0:
        o1.write(line)
    	o2.write(ts + "\n")
      else:
        o1.write(ts + "\n")
        o2.write(line)

def checkCondP2(line, o1, o2):
  if "trans" not in line and not "report" in line:
    o1.write(line)
    o2.write(line)
  else:
    ts = extractTs(line)
    if "trans" in line:
      val = extractVal(line, 1)
    else:
      val = extractVal(line, 0)
    if duplicates and val % 3 == 0:
        o1.write(line)
	o2.write(line)
    else:
      if val % 2 == 0:
	o2.write(ts + "\n")
	o1.write(line)
      else:
	o1.write(ts + "\n")
	o2.write(line)

def checkCondP3(line, o1, o2):
  if "trans" not in line and not "auth" in line:
    o1.write(line)
    o2.write(line)
  else:
    ts = extractTs(line)
    val = extractVal(line, 1)
    if duplicates and val % 3 == 0:
      o1.write(line)
      o2.write(line)
    else:
      if val % 2 == 0:
        o1.write(line)
        o2.write(ts + "\n")
      else:
        o1.write(ts + "\n")
        o2.write(line)

def processLine(line, o1, o2):
  policy = args.policy
  if policy == "P1":
    checkCondP1(line, o1, o2)
  elif policy == "P2":
    checkCondP2(line, o1, o2)
  elif policy == "P3":
    checkCondP3(line, o1, o2)

num_lines = sum(1 for line in open(args.input))
count = 0


with open (args.output + "-start.log", "w") as s:
  with open (args.output + "-left.log", "w") as o1:
    with open (args.output + "-right.log", "w") as o2:
      with open (args.output + "-save.log", "w") as o3:
        with open (args.output + "-resume.log", "w") as o4:
          with open (args.output + "-end.log", "w") as e:
            with open(args.input) as fp:
              for line in fp:
                count = count + 1
                if count < 0.35 * num_lines:
                  s.write(line)
                elif count < 0.6 * num_lines:
                  processLine(line, o1, o2)
                else:
                  e.write(line)

                if count < 0.43 * num_lines:
                  o3.write(line)
                else:
                  o4.write(line)

              s.write("> split_state (t:int),  (),(0)  (),(1) <")
              o1.write("> save_and_exit left-es <")
              o2.write("> save_and_exit right-es <")

              o3.write("> save_and_exit checkpoint <")
