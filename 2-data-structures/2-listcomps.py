# A quick way to build a sequence is using a list comprehension (if the target is a list) or a generator expression (for other kinds of sequences). 
# Listcomps and genexps make code more readable and often faster when its intent is explicit
"""
>>> symbols = '$¢£¥€¤'
>>> codes = [ord(symbol) for symbol in symbols]
>>> codes
[36, 162, 163, 165, 8364, 164]

>>> colors = ['black', 'white']
>>> sizes = ['S', 'M', 'L']
>>> tshirts = [(color, size) for color in colors for size in sizes]  
>>> tshirts
[('black', 'S'), ('black', 'M'), ('black', 'L'), ('white', 'S'), ('white', 'M'), ('white', 'L')]
>>> for tshirt in (f'{c} {s}' for c in colors for s in sizes):  
...     print(tshirt)
black S
black M
black L
white S
white M
white L
"""

# Use genexp if you don't need it in memory, it is more performant by yielding items one by one
#  using iterator protocol instead of building a whole list just to feed another constructor

if __name__ == "__main__":
    import doctest
    doctest.testmod()