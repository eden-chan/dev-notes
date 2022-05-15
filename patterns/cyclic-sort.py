"""
>>> cyclic_sort([3, 1, 5, 4, 2])
[1, 2, 3, 4, 5]
>>> find_missing_number([4,1,3,0])
2
>>> find_all_missing_numbers([2, 3, 0, 7, 2, 3, 5, 7])
[1, 4, 6]
>>> find_all_missing_numbers([5,3,4,0,1,2])
[]
"""

# 1 ... n
def cyclic_sort(nums):
  i = 0
  while i < len(nums):
    j = nums[i] - 1
    if nums[i] != nums[j]:
      nums[i], nums[j] = nums[j], nums[i]  # swap
    else:
      i += 1
  return nums



#  0...n
def find_missing_number(nums):
  i, n = 0, len(nums)
  while i < n:
    j = nums[i]
    if nums[i] < n and nums[i] != nums[j]:
      nums[i], nums[j] = nums[j], nums[i]  # swap
    else:
      i += 1

  # find the first number missing from its index, that will be our required number
  for i in range(n):
    if nums[i] != i:
      return i

  return n


#  0 ... n with duplicates
def find_all_missing_numbers(nums):
  i,n=0, len(nums)
  while i < n:
    j = nums[i] 
    if nums[i] < n and nums[i] != nums[j]:
      nums[i], nums[j] = nums[j], nums[i]
    else:
      i+=1 
  
  missing = []
  j=0
  for i in range(n):
    if nums[i] != j:
      missing.append(j)
    else:
      i+=1
    j+=1


  return missing 

if __name__ == "__main__":
    import doctest
    doctest.testmod()
    
    