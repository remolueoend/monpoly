from argparse import ArgumentParser
import sys

parser = ArgumentParser()
parser.add_argument("-f", "--file", help="Input log file")

args = parser.parse_args()

currentTp = 0
currentTs = 1

def validLine(line):
	if line.find("@") == 0:
		return 1
	else:
		return 0

def split_line(line):
  global currentTp
  global currentTs

  if validLine(line) == 0:
    return ""

  arr = line.split(" ")
  ts  = arr[0]
  ts  = currentTs
  name= arr[1]
  tp  = currentTp
  currentTp += 1
  val = arr[2]
  val = val[1:len(val)-2]

  currentTs += 10

  return produce_format (name, tp, ts, val)

def produce_format(name, tp, ts, val):
  arr = val.split(",")
  values = ",".join(list(map(lambda x: "x = " + x, arr)))

  return "%s, tp = %s, ts = %s, %s\n" % (name, tp, ts, values)


def processLine(line):
  sys.stdout.write(split_line(line))

with open(args.file, "r") as f:
  for line in f:
   processLine(line)
