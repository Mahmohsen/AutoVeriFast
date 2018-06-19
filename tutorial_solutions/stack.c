#include "stdlib.h"


//@ autogen stack = Many node
 

//The following predicates are auto generated 
/*@ 

predicate stack (struct stack *stack; int count) = 
stack->head |-> ?head &*& malloc_block_stack(stack) &*& node(head, count) &*& count >= 0; 

predicate node (struct node *node; int count) = 
 node == 0 ? count == 0 : node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node)  &*& node(next, ?count1) &*& count == count1 + 1 &*& count > 0; 
@*/


struct node {    			struct node *next;	
	int value;
};	

struct stack 
{    
	struct node *head;	
};


struct stack *create_stack()
    //@ requires true;
    //@ ensures true &*& stack(result,0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires true &*& stack(stack,?count0);
    //@ ensures true &*& stack(stack,(count0 + 1));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
   
}

int stack_pop(struct stack *stack)
    //@ requires true &*& stack(stack,?count0) &*& count0 > 0;
    //@ ensures true &*& stack(stack,count0-1);
{

    struct node *head = stack->head;
//@open node(head,count0); 
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

void stack_dispose(struct stack *stack)
    //@ requires true;
    //@ ensures true;
{

    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_pop(s);
    stack_pop(s);
    stack_dispose(s);
    return 0;
}
