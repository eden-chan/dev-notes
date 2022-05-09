
"""
Cartesian Products
>>> colors = ['black', 'white']
>>> sizes = ['S', 'M', 'L']
>>> for tshirt in (f'{c} {s}' for c in colors for s in sizes):  
...     print(tshirt)
black S
black M
black L
white S
white M
white L

 Using + and * with Sequences creates a new sequence
>>> l = [1, 2, 3]
>>> l + [4, 5]
[1, 2, 3, 4, 5]
>>> l * 5
[1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3]
>>> 5 * 'abcd'
'abcdabcdabcdabcdabcd'


# Tic Tac Toe board
>>> good_board = [['_'] * 3 for i in range(3)]  
>>> good_board
[['_', '_', '_'], ['_', '_', '_'], ['_', '_', '_']]
>>> good_board[1][2] = 'X'  
>>> good_board
[['_', '_', '_'], ['_', '_', 'X'], ['_', '_', '_']]

#  Be careful with references. 
>>> weird_board = [['_'] * 3] * 3  #1 outer list is made of three ref to the same inner list, so any modifications to one inner list modifies all refs to that same inner list. 
>>> weird_board
[['_', '_', '_'], ['_', '_', '_'], ['_', '_', '_']]
>>> weird_board[1][2] = 'O' #2 aliasing the same object
>>> weird_board
[['_', '_', 'O'], ['_', '_', 'O'], ['_', '_', 'O']]


# The problem with weird_board is it behaves like this code: 
row = ['_'] * 3
board = []
for i in range(3):
    board.append(row) # the same row is appended three times to board

# For good_board, it behaves like this code: 
>>> board = []
>>> for i in range(3):
...     row = ['_'] * 3  #1 each iteration builds a new row and appends it to board
...     board.append(row)
>>> board
[['_', '_', '_'], ['_', '_', '_'], ['_', '_', '_']]
>>> board[2][0] = 'X'
>>> board  #2 only row 2 is changed, as expected
[['_', '_', '_'], ['_', '_', '_'], ['X', '_', '_']]


# Augmented Assignment with Sequences (+= and *=)

__iadd__ and __imul__ are the special methods to implement
By default in a+=b, if a does not implement __iadd__ then a+=b has the same effect as a = a + b 
So a + b is evaluated firs, producing a new object that is then bound to a. 
Thus the identity of the object bound to a may or may not change, depending on the availability of __iadd__ 

In general, for mutable sequences, it is a good bet that __iadd__ is implemented and that += happens in place. For immutable sequences, clearly there is no way for that to happen.


# >>> l = [1, 2, 3]
# >>> id(l)
# 4311953800  # ID of initial list. NOTE: WILL FAIL since ID's are unique.
# >>> l *= 2
# >>> l
# [1, 2, 3, 1, 2, 3]
# >>> id(l) # the list is the same object with new items appended. NOTE: will fail since id's are unique
# 4311953800  
# >>> t = (1, 2, 3) 
# >>> id(t) # id of  nitial tuple (NOTE: tuples are immutable, see 3-tuples.py) NOTE: will fail since id's are unique
# 4312681568  
# >>> t *= 2
# >>> id(t)
# 4301348296  # after multiplication, a new tuple is created NOTE: will fail since id's are unique

# >>> t = (1, 2, [30, 40])
# >>> t[2] += [50, 60]
# TypeError: 'tuple' object does not support item assignment

# I thought it would yield (1, 2, [30, 40, 50, 60]) 😅
# UPDATE: NO, it does yield (1, 2, [30, 40, 50, 60]) AND IT ALSO THROWS THE TypeError: 'tuple' object does not support item assignment 😱
# https://pythontutor.com/ great tool for visualizing code execution

Here is the bytecode Python generates for s[a] += b
# >>> s = ['a']
# >>> b = 'b'
# >>> dis.dis('s[0] += b')
#   1           0 LOAD_NAME                0 (s)
#               3 LOAD_NAME                1 (a)
#               6 DUP_TOP_TWO
#               7 BINARY_SUBSCR                      
#               8 LOAD_NAME                2 (b)
#              11 INPLACE_ADD                        
#              12 ROT_THREE
#              13 STORE_SUBSCR                       
#              14 LOAD_CONST               0 (None)
#              17 RETURN_VALUE

Key Takeaways: 
Avoid putting mutable items in tuples.

Augmented assignment is not an atomic operation—we just saw it throwing an exception after doing part of its job.

Inspecting Python bytecode is not too difficult, and can be helpful to see what is going on under the hood.

"""

if __name__ == "__main__":
    import doctest
    doctest.testmod()
