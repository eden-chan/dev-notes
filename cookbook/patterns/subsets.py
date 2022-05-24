
n = 3
subset=[]

arr = [10,20,30]
def search(k):
    if k == n:
       print(subset) # process subset
    else:
        search(k+1)
        subset.append(arr[k])
        search(k+1)
        subset.pop(-1)

search(0)

if __name__ == "__main__":
    import doctest
    doctest.testmod()

