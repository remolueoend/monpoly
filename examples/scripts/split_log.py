from argparse import ArgumentParser

parser = ArgumentParser()
parser.add_argument("-f", "--file", help="LOGFILE to split")
parser.add_argument("-o", "--output", help="output file prefix")
parser.add_argument("-p", "--policy", help="according to which policy should the file be split")

args = parser.parse_args()

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
    if "publish" in line:
      val = extractVal(line, 1)
    else:
      val = extractVal(line, 1)
    if val % 2 == 0: o1.write(line)
    else: o2.write(line)

def checkCondP2(line, o1, o2):
  if "trans" not in line and not "report" in line:
    o1.write(line)
    o2.write(line)
  else:
    if "trans" in line:
      val = extractVal(line, 1)
    else:
      val = extractVal(line, 0)
    if val % 2 == 0: o1.write(line)
    else: o2.write(line)

def checkCondP3(line, o1, o2):
  if "trans" not in line and not "auth" in line:
    o1.write(line)
    o2.write(line)
  else:
    val = extractVal(line, 1)
    if val % 2 == 0: o1.write(line)
    else: o2.write(line)

def processLine(line, o1, o2):
  policy = args.policy
  if policy == "P1":
    checkCondP1(line, o1, o2)
  elif policy == "P2":
    checkCondP2(line, o1, o2)
  elif policy == "P3":
    checkCondP3(line, o1, o2)

print args.file

num_lines = sum(1 for line in open(args.file))
count = 0

with open (args.output + "-start.log", "w") as s:
  with open (args.output + "-left.log", "w") as o1:
    with open (args.output + "-right.log", "w") as o2:
      with open (args.output + "-end.log", "w") as e:
        with open(args.file) as fp:
          for line in fp:
            count = count + 1
            if count < 0.35 * num_lines:
              s.write(line)
            elif count < 0.6 * num_lines:
              processLine(line, o1, o2)
            else:
              e.write(line)

