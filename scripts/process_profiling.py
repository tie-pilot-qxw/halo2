from dataclasses import dataclass
from typing import Literal, Tuple, List, Callable
from sys import argv

@dataclass
class Event:
    typ: Literal['begin', 'end']
    t: int
    name: str

def parse_typ(s: str) -> Tuple[str, Literal['begin', 'end']]:
    if s.startswith("Begin"):
        return s[6:], 'begin'
    elif s.startswith("End"):
        return s[4:], 'end'
    else:
        raise RuntimeError("invalid typ: " + s)

def parse_name_time(s: str) -> Tuple[str, int]:
    name, t = s.split(": ")
    return name, int(t)

def parse_event(s: str) -> Event:
    s, typ = parse_typ(s)
    name, t = parse_name_time(s)
    return Event(typ, t, name)

@dataclass
class IntervalTree:
    begin: int
    end: int
    duration: int
    repeat: int
    name: str
    children: List['IntervalTree']

    @staticmethod
    def build(events: List[Event]) -> 'IntervalTree':
        def build_children(parent_begin: int, parent_name: str, children: List['IntervalTree'], events: List[Event]) -> Tuple['IntervalTree', List[Event]]:
            if len(events) == 0:
                raise RuntimeError("end of events")
            if events[0].typ == 'end' and events[0].name != parent_name:
                raise RuntimeError(f"no matching begin for {events[0].name}")
            if events[0].typ == 'end' and events[0].name == parent_name:
                return IntervalTree(parent_begin, events[0].t, events[0].t - parent_begin, 1, parent_name, children), events[1:]

            first_child, rest_events = build_children(events[0].t, events[0].name, [], events[1:])
            children.append(first_child)
            return build_children(parent_begin, parent_name, children, rest_events)
        
        if len(events) == 0:
            raise RuntimeError("end of events")
        interval, rest = build_children(events[0].t, events[0].name, [], events[1:])
        return interval
            
    
    @staticmethod
    def collapsed_children(children: List['IntervalTree']) -> List['IntervalTree']:
        def recurse(children: List['IntervalTree'], collapsed: List['IntervalTree']):
            if len(children) == 0:
                return

            if len(collapsed) == 0:
                collapsed.append(children[0])
                return recurse(children[1:], collapsed)
            
            if children[0].name == collapsed[-1].name and len(children[0].children) == 0 and len(collapsed[-1].children) == 0:
                collapsed[-1].end = children[0].end
                collapsed[-1].duration += children[0].duration
                collapsed[-1].repeat += 1
                return recurse(children[1:], collapsed)
            
            collapsed.append(children[0])
            return recurse(children[1:], collapsed)

        r = []
        recurse(children, r)
        return r


    def print(self, total: int, f: Callable[[str], None]=print):
        def recurse(depth: int, interval: 'IntervalTree'):
            percentage = float(interval.duration) / float(total)
            repeat = "" if interval.repeat == 1 else f"(x{interval.repeat})"
            f(f"{'    ' * depth}{interval.name}{repeat} {interval.duration} ({percentage * 100:.2f}%)")

            for child in IntervalTree.collapsed_children(interval.children):
                recurse(depth + 1, child)
        recurse(0, self)

            
if __name__ == "__main__":
    if len(argv) != 2:
        print("usage: <prog> input_file")
    
    with open(argv[1], 'r') as rf:
        s = rf.read()
    
    lines = s.split('\n')
    events = [parse_event(line) for line in lines]
    interval = IntervalTree.build(events)
    interval.print(total = interval.duration)


