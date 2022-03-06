# A quick way to build a sequence is using a list comprehension (if the target is a list) or a generator expression (for other kinds of sequences). 
# Listcomps and genexps make code more readable and often faster when its intent is explicit
"""
>>> symbols = '$¢£¥€¤'
>>> codes = [ord(symbol) for symbol in symbols]
>>> codes
[36, 162, 163, 165, 8364, 164]
"""
if __name__ == "__main__":
    import doctest
    doctest.testmod()