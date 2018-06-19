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



//*******************************************************************************************************************************************
//find a link with given key

struct node* find(int key, struct node* head, struct node* head1)
//@requires true;
//@ensures true;
{

   struct node* current = head;
   if(head == NULL)
	{
      return NULL;
   }
   int x;
   while(current->key != key)
   //@ requires true ;
   //@ ensures  true;
  {
      if(current->next == NULL){
         abort();
      }else {
         current = current->next;
      }
   }      

   return current;
}


