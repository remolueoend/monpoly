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
    arr[0] = "@" + str(currentTs)

    currentTs += 10

    return " ".join(arr)

def processLine(line):
    sys.stdout.write(split_line(line))

with open(args.file, "r") as f:
    for line in f:
        processLine(line)
