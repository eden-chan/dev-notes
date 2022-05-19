"""
Six cases

- A & B = ∅
- A & B ≠ ∅ 
- B ⊂ A
- B & A ≠ ∅
- A ⊂ B
- B & A = ∅ 

>>> Interval(1,2)
[1, 2]

Given a list of intervals, merge all the overlapping intervals to produce a
list that has only mutually exclusive intervals.

>>> merge([Interval(1,2), Interval(2,3), Interval(4,5)])
[[1, 3], [4, 5]]

>>> insert(Interval(0,2), [Interval(1,3), Interval(4,5)])
[[0, 3], [4, 5]]
>>> insert(Interval(0,4), [Interval(1,3), Interval(4,5)])
[[0, 5]]
>>> insert(Interval(6,7), [Interval(1,3), Interval(4,5)])
[[1, 3], [4, 5], [6, 7]]

Since we sort the intervals, our algorithm will take O(N * logN)
O(N∗logN)
.

"""

class Interval:
    def __init__(self, start, end):
        self.start = start
        self.end = end

    def __repr__(self):
        return f"[{self.start}, {self.end}]"


def merge(intervals):
    if len(intervals) < 2:
        return intervals

    # sort the intervals on the start time
    intervals.sort(key=lambda x: x.start)

    # Add previous interval if the current one is non-overlapping 
    mergedIntervals = []
    start = intervals[0].start
    end = intervals[0].end
    for i in range(1, len(intervals)):
        interval = intervals[i]
        if interval.start <= end: 
            end = max(interval.end, end)
        else:  
            mergedIntervals.append(Interval(start, end))
            start = interval.start
            end = interval.end

    # add the last interval
    mergedIntervals.append(Interval(start, end))
    return mergedIntervals

# assume intervals are sorted



#     for i in range(0, len(intervals)):
def insert(new_interval,intervals):
    merged = []
    i, start, end = 0, 0, 1

    # skip (and add to output) all intervals that come before the 'new_interval'
    while i < len(intervals) and intervals[i].end < new_interval.start:
        merged.append(intervals[i])
        i += 1

    # merge all intervals that overlap with 'new_interval'
    while i < len(intervals) and intervals[i].start <= new_interval.end:
        new_interval.start = min(intervals[i].start, new_interval.start)
        new_interval.end = max(intervals[i].end, new_interval.end)
        i += 1

        # insert the new_interval
    merged.append(new_interval)

    # add all the remaining intervals to the output
    while i < len(intervals):
        merged.append(intervals[i])
        i += 1
    return merged

if __name__ == "__main__":
    import doctest
    doctest.testmod()

