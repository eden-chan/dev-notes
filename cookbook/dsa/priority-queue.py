"""
Problem
Implement a queue that sorts items by a given priority and 
always returns the item with the highest priority on each pop operation.

"""

import heapq

class PriorityQueue:
    def __init__(self):
        self._queue = []
        self._index = 0

    def push(self, item, priority):
        heapq.heappush(self._queue, (-priority, self._index, item))
        self._index += 1

    def pop(self):
        return heapq.heappop(self._queue)[-1]
        
if __name__ == "__main__":
    import doctest
    doctest.testmod()
