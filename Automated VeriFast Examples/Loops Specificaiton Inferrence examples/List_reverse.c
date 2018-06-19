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
//The following function takes a list and return the list reversed.

struct node* reverse(struct node* head) 
//@ requires true;
//@ ensures true;
{
   struct node* prev   = NULL;
   struct node* current = head;
   struct node* next;
	
   while (current != NULL) 
   //@ requires true;
   //@ ensures  true;
   {
      next  = current->next;  
      current->next = prev;   
      prev = current;
      current = next;
   }

   head = prev;
   return head;	
}
