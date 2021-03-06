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

void printList(const struct node* head)
//@ requires true;
//@ ensures true;
{
   struct node *ptr = head;
   printf("\n[ ");
	
   while(ptr != NULL)
   //@ requires true;
   //@ ensures true;
   {     
      printf("(%d,%d) ",ptr->key,ptr->data);
      ptr = ptr->next;
   }	
   printf(" ]");
}

