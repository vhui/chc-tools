"""A parser for vampire output."""

import logging
import re
from collections import namedtuple
import json
from enum import Enum
import sys

class EType(Enum):
    EXP_LVL = 0
    EXP_POB = 1
    ADD_LEM = 2
    PRO_LEM = 3
    NA = 4
class ParsedLine (object):
    def __init__(self, lineType, unitId, unitString, inferenceRule, parents, statistics):
        self.lineType = lineType
        self.unitId = unitId
        self.unitString = unitString
        self.inferenceRule = inferenceRule
        self.parents = parents
        self.statistics = statistics

    def to_json(self):
        return {
            'lineType': self.lineType,
            'unitId' : self.unitId,
            'unitString' : self.unitString,
            'inferenceRule' : self.inferenceRule,
            'parents' : self.parents,
            'statistics' : self.statistics
        }

class Event (object):
    def __init__(self, idx, parent = None):
        self.lines = []
        self.idx = idx
        self.event_type = EType.NA
        self.parent = 0
        self.children = []
        self.exprID = -1
        self.pobID = -1
        self.level = -1
    def add_line(self, line):
        self.lines.append(line)

    def finalize(self, all_events):
        if self.lines[0].startswith("* LEVEL"):
            self.event_type = EType.EXP_LVL
            self.level = int(self.lines[0].strip().split()[-1])
        elif self.lines[0].startswith("** expand-pob"):
            self.event_type = EType.EXP_POB
            _, _, _, label1, level, label2, depth, label3, exprID, label4, pobID = self.lines[0].strip().split()[:11]
            assert(label1=="level:")
            self.level = int(level)
            assert(label2=="depth:")
            self.depth = int(depth)
            assert(label3=="exprID:")
            self.exprID = int(exprID)
            assert(label4=="pobID:")
            if pobID == 'none':
                self.pobID = -1
            else:
                self.pobID = int(pobID)
 
        elif self.lines[0].startswith("** add-lemma"):
            _, label0, level, label1, exprID, label2, pobID = self.lines[0].strip().split()[:7]
            assert(label0=="add-lemma:")
            if level == "oo":
                self.level = level
            else:
                self.level = int(level)
            assert(label1=="exprID:")
            self.exprID = int(exprID)
            assert(label2=="pobID:")
            self.pobID = int(pobID)
            self.event_type = EType.ADD_LEM
        elif self.lines[0].startswith("Propagating"):
            self.event_type = EType.PRO_LEM
        parent_event = self.find_parent(all_events)
        parent_event.children.append(self.idx)
        self.parent = parent_event.idx
        
    def find_parent(self, all_events):
        #Return None if the node should be merged with the parent
        #Return the parent otherwise
        if self.event_type == EType.ADD_LEM:
            #Adding lemma is the child event of the latest EXP_POB or Propagating
            if all_events[-1].event_type == EType.EXP_POB:
                return all_events[-1]
            else:
                for e in reversed(all_events):
                    if e.event_type == EType.PRO_LEM:
                        return e
        elif self.event_type == EType.EXP_POB:
           # is the child of the previous one if level = prev_level-1
            prev_event = all_events[-1]
            if prev_event.event_type == EType.EXP_POB and prev_event.level == self.level + 1:
                return prev_event
            # else, find the latest one with greater level
            for e in reversed(all_events):
                if e.event_type == EType.EXP_LVL:
                    return e
                elif e.event_type == EType.EXP_POB and e.level > self.level:
                    return e

            # only expect this to happen once because 'enter level 0' event is not produced
            print(self.lines)
            print("no father pob!!!!")
           
        elif self.event_type == EType.PRO_LEM:
            #Propagating is the child event of the latest EXP_LVL event
            for e in reversed(all_events):
                if e.event_type == EType.EXP_LVL:
                    return e

        return all_events[0]



    def to_Json(self):
        if self.event_type==EType.ADD_LEM:
            expr = "".join(self.lines[2:])
        else:
            expr = "".join(self.lines[1:])
        return {"nodeID": self.idx,
                "parent": self.parent,
                "children": self.children,
                "event_type": str(self.event_type),
                "expr": expr,
                "level": self.level,
                "exprID": self.exprID,
                "pobID": self.pobID,
                "to_be_vis": True}

def parse(lines):
    timer = 1
    all_events = [Event(0)]
    event = Event(idx = timer)

    for line in lines:
        if line.strip()=="":
            if len(event.lines)!=0: #not an empty event
                event.finalize(all_events)
                all_events.append(event)
                timer+=1
                event = Event(idx = timer)
            
        else:
            event.add_line(line)

    spacer_nodes = {}
    for event in all_events:
        spacer_nodes[event.idx] = event.to_Json()

    return spacer_nodes

if __name__=="__main__":
    file_name = "/home/turingdreams/Documents/Research_UofT/PreCond_CC3/library/spacer.log" #.z3-trace 
    if len(sys.argv) > 1:
        file_name = sys.argv[1]
    with open(file_name, "r") as f:
        lines = f.readlines()
        all_events = parse(lines)
        print(len(all_events))
        # for e in all_events[:10]:
        #     print(e.to_Node())
