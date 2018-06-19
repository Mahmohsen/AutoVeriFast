#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <malloc.h>
#include <math.h>





//The following predicates are auto generated 
/*@ 

predicate node (struct node *node; int count) = 
 node == 0 ? count == 0 : node->data |-> ?data &*& node->key |-> ?key &*& node->next |-> ?next &*& malloc_block_node(node)  &*& node(next, ?count1) &*& count == count1 + 1; 


@*/


struct node  {      char data;
   int key;   
   struct node *next;
};



//****************************************************************************************************************************


// return the length of a linked list
void length(struct node* head, int length)
//@requires true;
//@ensures true;
{
   if(head == 0){abort();}
   length = 0;
   struct node *current;
   for(current = head; current != NULL; current = current->next)
   //@requires true;
   //@ensures true;
   {
      length++;
   }
}



