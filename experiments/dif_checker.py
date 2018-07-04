from argparse import ArgumentParser
from sets import Set

parser = ArgumentParser()
parser.add_argument("-f1", "--file1", help="First file to compare")
parser.add_argument("-f2", "--file2", help="Second file to compare")

args = parser.parse_args()

def validLine(line):
	if line.find("@") == 0:
		return 1
	else:
		return 0

def extractFingerprint(line):
	arr = line.split(" ")

	ts=arr[0]
	tp=arr[3]
	val=arr[4]

	ts=ts[1:len(ts) - 1]
	tp=tp[0:len(tp) - 2]
	val=val[0:len(val)-1]

	return ts+"."+val

def processLine(line, set):
	if validLine(line):
		fp = extractFingerprint(line)
		set.add(fp)

reference = Set()
combined  = Set()

with open(args.file1, "r") as f1:
	for line in f1:
		processLine(line, reference)

with open(args.file2, "r") as f2:
	for line in f2:
		processLine(line, combined)

print "Info: Number of unique entries in reference result: " + str(len(reference))
print "Info: Number of unique entries in experiment result: " + str(len(combined))

dif = reference.difference(combined)
print "Info: False Negatives (" + str(len(dif)) + ")"
print dif

dif = combined.difference(reference)
print "Info: False Positives (" + str(len(dif)) + ")"
print dif


