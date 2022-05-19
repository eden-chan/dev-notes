
"""
Problem
keep a limited history of the last few items seen during iteration or during some other kind of processing.

limited history is a perfect use for a collections.deque
>>> q = deque(maxlen=3)
>>> q.append(1)
>>> q.append(2)
>>> q.append(3)
>>> q
deque([1, 2, 3], maxlen=3)
>>> q.append(4)
>>> q
deque([2, 3, 4], maxlen=3)
>>> q.append(5)
>>> q
deque([3, 4, 5], maxlen=3)
Although you could manually perform such operations on a list
(e.g., appending, deleting, etc.), the queue solution is far more elegant and runs a lot faster.

"""



if __name__ == "__main__":
    import doctest
    doctest.testmod()

