
"""
>>> head = Node(1)
>>> head.next = Node(2)
>>> head.next.next = Node(3)

>>> has_cycle(head)
False
>>> find_cycle_length(head)
0
>>> head.next.next.next = head
>>> has_cycle(head)
True
>>> find_cycle_length(head)
3
>>> head.next.next.next = Node(4)
>>> head.next.next.next.next = head.next.next
>>> has_cycle(head)
True
>>> find_cycle_length(head)
2

"""


class Node:
  def __init__(self, value, next=None):
    self.value = value
    self.next = next


def has_cycle(head):
  slow, fast = head, head
  while fast is not None and fast.next is not None:
    fast = fast.next.next
    slow = slow.next
    if slow == fast:
      return True  # found the cycle
  return False


def find_cycle_length(head):
  slow, fast = head, head
  while fast is not None and fast.next is not None:
    fast = fast.next.next
    slow = slow.next
    if slow == fast:  # found the cycle
      return calculate_cycle_length(slow)

  return 0


def calculate_cycle_length(slow):
  current = slow
  cycle_length = 0
  while True:
    current = current.next
    cycle_length += 1
    if current == slow:
      break
  return cycle_length


if __name__ == "__main__":
    import doctest
    doctest.testmod()
