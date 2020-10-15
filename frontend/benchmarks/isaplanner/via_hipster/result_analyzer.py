import os
import re
SRC_DIR = "/home_local/guest-9530/Apps/benchmarks/benchmarks/tip2015thy_results"
DST_DIR = "/home_local/guest-9530/Apps/benchmarks/benchmarks/tip2015thy_lemmas"
HR_TO_MIN = 60
MIN_TO_SEC = 60


def isLog(fileName):
    return ".log" in fileName

def isError(fileName):
    return ".err" in filename

def isTime(fileName):
    return ".time" in filename

#converts time from format hh:mm:ss.ms to seconds in integer
def convStringToTime(timeStr):
    time_list = timeStr.split(":")
    hr = int(time_list[0])
    min = int(times_list[1])
    sec = float(times_list[2])
    return float(hr*HR_TO_MIN*MIN_TO_SEC) + float(min*MIN_TO_SEC) + sec

def countQuotes(line):
    counter = 0
    for letter in line:
        if letter == '"':
            counter += 1
    return counter
  
def getLemmasAndErrors(logFile):
    lemmaList = []
    unknownList = []
    midLemma = False
    midUnknown = False
    currLemma = ""
    for line in logFile:
        if midLemma:
            currLemma += line
            lemmaList.append(currLemma)
            currLemma = ""
            midLemma = False
            continue
        if midUnknown:
            currLemma += line
            unknownList.append(currLemma)
            currLemma = ""
            midUnknown = False
            continue
        if "lemma lemma" in line:
            if countQuotes(line) == 1:
                currLemma += line
                midLemma = True
                continue
            lemmaList.append(line)
        if "lemma unknown" in line:
            if countQuotes(line) == 1:
                currLemma += line
                midUnknown = True
                continue
    
    return (lemmaList,unknownList)
                
def writeToFile(infoList, f):
    for line in infoList:
        f.write(line)

def exportLemmas():
    fileNames = os.listdir(args.inp_dir)
    logFileNames = filter(isLog, fileNames)
    #errFileNames = filter(isErr, filenames)
    #timeFileNames = filter(isTime, filenames)
    
    for logName in logFileNames:
        fileSubject = logName[:-8]
        lemmaFileName = fileSubject + " lemmas.txt"
        oopsFileName = fileSubject + " oops.txt"
        log_path = args.inp_dir + "/" + logName
        lemma_path = args.out_dir + "/" + lemmaFileName
        oops_path = args.out_dir + "/" + oopsFileName
        
        logFile = open(log_path, 'r')
        lemmaFile = open(lemma_path,'w')
        oopsFile = open(oops_path,'w')
        
        (lemmaList, unknownList) = getLemmasAndErrors(logFile)
        
        writeToFile(lemmaList, lemmaFile)
        writeToFile(unknownList, oopsFile)
        oopsFile.close()
        lemmaFile.close()
        logFile.close()

def logContainsException(file):
    for line in file:
        if "Exception" in line and "raised" in line: #better use regex
            return True
    return False

def printErrorLogs():
    fileNames = os.listdir(SRC_DIR)
    logFileNames = filter(isLog, fileNames)
    for logName in logFileNames:
        log_path = SRC_DIR + "/" + logName
        logFile = open(log_path, 'r')
        if logContainsException(logFile):
            print(logName)
        logFile.close()

def logContainsTime(file):
    for line in file:
        if "elapsed time" in line:
            return True
    return False

def printCountFinishedLogs():
    fileNames = os.listdir(SRC_DIR)
    logFileNames = filter(isLog, fileNames)
    counter = 0
    for logName in logFileNames:
        log_path = SRC_DIR + "/" + logName
        logFile = open(log_path, 'r')
        if logContainsTime(logFile):
            counter += 1
        logFile.close()
    print(counter)   
    
import argparse

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command")
    parser.add_argument("-i", "--inp_dir", default = SRC_DIR)
    parser.add_argument("-o", "--out_dir", default = DST_DIR)
    global args
    args = parser.parse_args()
    if not os.path.exists(args.out_dir):
        os.makedirs(args.out_dir)
    commandDict = {"exportLemmas": exportLemmas, 
    "printErrorLogs": printErrorLogs, "countFinishedLogs": printCountFinishedLogs}
    func = commandDict.get(args.command)
    func()
    

main()
    
