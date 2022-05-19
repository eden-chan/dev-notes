"""
>>> a = Node()
>>> a.next = Node(1)
>>> a.next.next = Node(2)
>>> a
0, 1, 2, 
>>> reverse(a)
2, 1, 0, 

>>> b = Node(0, Node(1, Node(2, Node(3, Node(4, Node(5))))))
>>> reverse_sublist(b, p=1, q=4)
0, 4, 3, 2, 1, 5, 

"""
class Node:
        
    def __init__(self, val=0, next=None):
        self.val=val 
        self.next=next 
    
    def __repr__(self) -> str:
        return f"{self.val}, {'' if self.next is None else self.next}"

def reverse(head):
    
    prev,cur,_next=None,head,None 

    while cur is not None:
        _next = cur.next 
        cur.next = prev 
        prev = cur 
        cur = _next
    return prev 
        
    
def reverse_sublist(head):
    prev,cur,_next=None,head,None
    
    # move up to index p
    while cur 

    # reverse list starting from p to q
    # set next of last of reversed sublist to remainder of list



        

if __name__ == "__main__":
    import doctest
    doctest.testmod()
    