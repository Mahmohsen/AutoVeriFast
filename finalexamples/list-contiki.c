/*
 * Copyright (c) 2004, Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE


 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 *
 * Author: Adam Dunkels <adam@sics.se>
 *
 */

/**
 * \file
 * Linked list library implementation.
 *
 * \author Adam Dunkels <adam@sics.se>
 *
 */

/**
 * \addtogroup list
 * @{
 */

#include "list.h"
#include "stdlib.h"
#include "assert.h"
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <malloc.h>
#include <math.h>

//The following predicates are auto generated 
/*@ 

//predicate list (struct list *list; int count) = 
// list == 0 ? count == 0 : list->next |-> ?next &*& malloc_block_list(list)  &*& list(next, ?count1) &*& count == count1 + 1; 


@*/





/*---------------------------------------------------------------------------*/
/**
 * Initialize a list.
 *
 * This function initalizes a list. The list will be empty after this
 * function has been called.
 *
 * \param list The list to be initialized.
 */
void list_init(list_t list)
//@requires true &*& pointer(list,?count0);
//@ensures true &*& pointer(list,0);
{
  *list = NULL;
}
/*---------------------------------------------------------------------------*/
/**
 * Get a pointer to the first element of a list.
 *
 * This function returns a pointer to the first element of the
 * list. The element will \b not be removed from the list.
 *
 * \param list The list.
 * \return A pointer to the first element on the list.
 *
 * \sa list_tail()
 */
void *list_head(list_t list)
//@requires true &*& pointer(list,?count0) &*& count0 > 0;
//@ensures true &*& pointer(list, count0);
{
  return *list;
}
/*---------------------------------------------------------------------------*/
/**
 * Duplicate a list.
 *
 * This function duplicates a list by copying the list reference, but
 * not the elements.
 *
 * \note This function does \b not copy the elements of the list, but
 * merely duplicates the pointer to the first element of the list.
 *
 * \param dest The destination list.
 * \param src The source list.
 */
void list_copy(list_t dest, list_t src)
//@requires pointer(src,?count0) &*& pointer(dest,?count1);
//@ensures pointer(src,count0) &*& pointer(dest,count0);
{
  *dest = *src;
}
/*---------------------------------------------------------------------------*/
/**
 * Get the tail of a list.
 *
 * This function returns a pointer to the elements following the first
 * element of a list. No elements are removed by this function.
 *
 * \param list The list
 * \return A pointer to the element after the first element on the list.
 *
 * \sa list_head()
 */
void *list_tail(list_t list)
//@requires true &*& pointer(list,?head) &*& lseg(head,0,?count);
//@ensures true &*& pointer(list,head) &*& result == NULL? head == 0 : lseg(head,?l,_) &*& l->next |-> ?next1 &*& malloc_block_list(l) &*& result == l &*& next1 == NULL;
{
  struct list *l;
  
  if(*list == NULL) {
    return NULL;
  }
  //@assert list != NULL;
  for(l = *list; l->next != NULL;)
  //@requires true &*& pointer(list,head) &*& lseg(head,l,_) &*& l->next |-> ?next &*& malloc_block_list(l) &*& lseg(next,0,_) &*& head != 0 &*& l != 0; //&*& list_next(l, ?next) &*& malloc_block_list(l) &*& lseg(next,0,_) &*& list != NULL &*& l!= NULL; 
  //@ensures true &*& pointer(list,head) &*& lseg(head,l,_) &*& l->next |-> ?next1 &*& malloc_block_list(l) &*& lseg(next1,0,_) &*& next1 == NULL;//&*& malloc_block_list(old_l) &*& list_next(old_l,next) &*& lseg(next,0,_) &*& l!= NULL;  {
  {
  	//@close lseg(next,next,_);
        //@struct list* temp = l;
  	l = l->next;
  	//@open lseg(next,0,_);
  	//@close lseg(temp,l,_);
  	//@close lseg(next,0,_);
  	//@lseg_append(head);
  	//@open lseg(next,0,_);

  }
  //@assert l != NULL;
  return l;
}
/*---------------------------------------------------------------------------*/
/**
 * Add an item at the end of a list.
 *
 * This function adds an item to the end of the list.
 *
 * \param list The list.
 * \param item A pointer to the item to be added.
 *
 * \sa list_push()
 *
 */
void list_add(list_t list, void *item)
//@requires true &*& pointer(list,?head) &*& lseg(head,0,?count0) &*& lseg(item,0,1) &*& item != NULL;
//@ensures true &*& pointer(list,?head1) &*& lseg(head1,0,?count01);
{
  struct list *l;

  /* Make sure not to add the same element twice */
  list_remove(list, item);
  
  //@struct list* temp = ((struct list *)item)->next;
  ((struct list *)item)->next = NULL;
  //@leak lseg(temp,0,_);
 
  l = list_tail(list);
  if(l == NULL) {
    *list = item;
  } else {
    l->next = item;
    //@assert pointer(list,?head1);
    //@lseg_append_final(head1);
  }
}
/*---------------------------------------------------------------------------*/
/**
 * Add an item to the start of the list.
 */
void list_push(list_t list, void *item)
//@requires true &*& pointer(list,?head) &*& lseg(head,0,?count1) &*& lseg(item,0,1) &*& item != NULL;
//@ensures true &*& pointer(list,?head1) &*& lseg(head1,0,_);
{
  /*  struct list *l;*/

  /* Make sure not to add the same element twice */

   list_remove(list, item);
   //@open lseg(item,0,1);
   //@struct list* temp = ((struct list *)item)->next ;
   //@open lseg(temp,0,_);
  ((struct list *)item)->next = *list;
  *list = item;
  //@leak lseg(temp,0,_);
  
}

//written by Mahmoud Mohsen
 
 
//lemma void lseg_contain(void *head)
//	requires head != NULL &*& list_next(head,?next0) &*& malloc_block_list(head) &*& lseg(next0, ?r, ?p,_) &*& r != NULL &*& malloc_block_list(r) &*& p(head) &*& p(r) &*& list_next(r,?next1) &*& lseg(next1,0,p,_);
//	ensures list_next(head,next0) &*& lseg(next0, r, p,_) &*& list_next(r,next1) &*& lseg(next1,0,p,_) &*& next1 != head;
//{
//	close lseg(r,0,p,_);
//	close lseg(head,0,p,_);
//	open lseg(head,r,p,_);
//	open lseg(r,0,p,_);
//} 
 
//predicate p(struct list* item) = item->next|-> ?next &*& malloc_block_list(item);

/*@

lemma void lseg_append(void *n1)
    requires lseg(n1, ?n2, _) &*& lseg(n2, ?n3, _) &*& lseg(n3, 0, _);
    ensures lseg(n1, n3, _) &*& lseg(n3, 0, _);
{
    open lseg(n1, n2, _);
    if (n1 == n2) {
    } else {
        assert pointer(n1, ?n1Next);
        lseg_append(n1Next);
        if (n3 != 0) {
            open lseg(n3, 0, _);
            pointer_distinct(n1, n3);
            close lseg(n3, 0, _);
        }
        close lseg(n1, n3, _);
    }
}

lemma void lseg_append1(void *head, void *second)
	requires lseg(head,second,_) &*& lseg(second, ?last,_) &*& lseg(last, ?third,_) &*& lseg(third, 0,_) &*& last != third &*& second != last &*& last != NULL;
	ensures lseg(head,last,_) &*& lseg(last, third,_) &*& lseg(third,0,_);
{
	open lseg(head,second,_);
	if(head == second)
	{
	}
	else
	{
		assert pointer(head, ?headnext);
		if(headnext != second)
		{
			open lseg(second, last,_);
			//close lseg(second, last,p, _);
			pointer_distinct(head,second);
			close lseg(second, last, _);
			lseg_append1(headnext,second);
			
		//open lseg(second,second, p,_);		
		}
		if(last != 0)
		{
			open lseg(last,third,_);
			pointer_distinct(head,last);
			close lseg(last,third,_);
		}
		if(headnext == second)
		{
			open lseg(headnext,second,_);
		}
		close lseg(head, last,_);
	}
}



lemma void lseg_append_final(void *n1)
    requires lseg(n1, ?n2, _) &*& lseg(n2, 0, _);
    ensures lseg(n1, 0, _);
{
    close lseg(0, 0, _);
    lseg_append(n1);
    open lseg(0, 0, _);
}



lemma void appendtoend(void *head)
	requires lseg(head,?l,_) &*& list_next(l,?next) &*& malloc_block_list(l) &*& list_next(next,?next1) &*& malloc_block_list(next) &*& malloc_block_list(next1) &*& next!= l;
	ensures lseg(head,next,_) &*& malloc_block_list(next) &*& malloc_block_list(next1) &*& list_next(next,next1);
{
	open lseg(head,l,_);
	assert pointer(head,?nl);
	if(head != l)
	{
		struct list* temp = head;
		appendtoend(temp->next);
	}
	close lseg(head,next,_);
}



@*/
/*---------------------------------------------------------------------------*/
/**
 * Remove the last object on the list.
 *
 * This function removes the last object on the list and returns it.
 *
 * \param list The list
 * \return The removed object
 *
 */
void *list_chop(list_t list)
//@requires true &*& pointer(list,?head0) &*& lseg(head0,0,_);
//@ensures true &*&  pointer(list,?head1) &*& (head1 == 0 ? lseg(result,0,_) : lseg(result,0,_) &*& lseg(head0,0,_));
{
  struct list *l;
  struct list *r;
  
  if(*list == NULL) {
    return NULL;
  }
  //@open lseg(head0,0,_);
  if(((struct list *)*list)->next == NULL) {
    l = *list;
    *list = NULL;
    //@close lseg(0,0,_);
    //@close lseg(l,0,_);
    return l;
  }

  for(l = *list;  l->next->next != NULL;)
  //@requires pointer(list,head0) &*& lseg(head0,l,_) &*& malloc_block_list(l) &*&  l->next|-> ?next1 &*& malloc_block_list(next1) &*& next1->next |-> ?next2 &*& lseg(next2,0,_) &*& l != NULL &*& next1 != NULL &*& head0 != NULL;
  //@ensures pointer(list,head0) &*& lseg(head0,l,_) &*& l->next|-> ?next3 &*& next3->next |-> ?next4 &*& lseg(next4,0,_) &*& malloc_block_list(l) &*& malloc_block_list(next3) &*& next3 != NULL &*& next4 == NULL;
  {
	l = l->next;
	//@open lseg(next2,0,_);	
	//@appendtoend(head0);
  }
  //@assert l->next->next  == NULL;
  r = l->next;
  l->next = NULL;
  //@close lseg(r,0,_);
  //@close lseg(l,0,_);
  //@lseg_append_final(head0);
  return r;
}
/*---------------------------------------------------------------------------*/
/**
 * Remove the first object on a list.
 *
 * This function removes the first object on the list and returns a
 * pointer to it.
 *
 * \param list The list.
 * \return Pointer to the removed element of list.
 */
/*---------------------------------------------------------------------------*/
void *list_pop(list_t list)
//@requires true &*& pointer(list,?head) &*& lseg(head,0,_);
//@ensures true &*& (head == 0 ? pointer(list,head) &*& lseg(head,0,_) : pointer(list,?head1) &*& lseg(head1,0,_) &*& list_next(head,?next) &*& malloc_block_list(head));//list(result,count1-0);
{
  //@struct list* temp = head;
  struct list *l;
  l = *list;
  if(*list != NULL) {
    *list = ((struct list *)*list)->next;
    }
  
  return l;
}
/*---------------------------------------------------------------------------*/
/**
 * Remove a specific element from a list.
 *
 * This function removes a specified element from the list.
 *
 * \param list The list.
 * \param item The item that is to be removed from the list.
 *
 */
/*---------------------------------------------------------------------------*/




void list_remove(list_t list, void *item)
//@requires true &*& pointer(list,?head0) &*& lseg(head0,NULL, ?count1); 
//@ensures true &*& pointer(list,?head1) &*& lseg(head1,NULL, ?count2);
{
  struct list *l;
  struct list *r;
  
  if(*list == NULL) {
    return;
  }
  
  r = NULL;
  for(l = *list; l != NULL;) 
   //@requires true &*& pointer(list,head0) &*& head0 != NULL &*& l != r &*& (l == head0 ? (lseg(l,0,_) &*& r == NULL) : (r!= NULL &*& (r != head0 ? lseg(head0,r,_) &*& /*(l == NULL ? lseg(r,0,p,_) &*& lseg(l,0,p,_) : lseg(r,l,p,_)*/ lseg(r,l,_) &*& lseg(l,0,_) : lseg(head0,r,_) &*& lseg(r,l,_) &*& lseg(l,0,_)) /* (l == NULL ? true : lseg(l,0,p,_)))))*/));
   //@ensures true &*& pointer(list,head0) &*& head0 != NULL &*& r != NULL &*& /*(l == NULL ? lseg(head0,r,p,_) &*& lseg(r,0,p,_) :*/ lseg(head0,r,_) &*& lseg(r,l,_) &*& lseg(l,0,_);
   {

    if(l == item) {
      if(r == NULL) {
	/* First on list */
	//@open lseg(l,0,_);
	*list = l->next;
      } else {
	//@assert l != head0;
	/* Not first on list */
	//@open lseg(r,l,_);
	//@open lseg(l,0,_);
	r->next = l->next;
      }
      abort();  
    }
     //@open lseg(l,0,_);    
     //@ if(l != head0) {open lseg(head0,r,_);open lseg(r,l,_);}
     //@ struct list *temp = r;
     //@assert r != l;
     r = l;  
     l = l->next;
     //@struct list *temp1 = *list;
     //@if(l != NULL) {open lseg(l,0,_);close lseg(l,0,_);}
     //@if(r == head0) {/*if(l != NULL) {close lseg(r->next,l,p,_);};*/ close lseg(r->next,l,_); close lseg(head0,r,_); close lseg(r,l,_); /*close lseg(l,0,p,_);*//* close lseg(l,0,p,_);*/} else {/*if(l != NULL) {close lseg(r->next,l,p,_);};*/ /*close lseg(r,r->next,p,_);*/ close lseg(temp,r,_); /*if(r != head0) {close lseg(r,0,p,_);};*/close lseg(l,l,_); close lseg(r,l,_); if(temp != head0) {lseg_append1(temp1->next,temp);/* if(r!= head0){open lseg(r,0,p,_);}; close lseg(l,l,p,_); close lseg(r,l,p,_);*/ /*close lseg(temp1->next,temp1->next,p,_);*/ close lseg(head0,r,_);} /*close lseg(r,l,p,_);*/ /*if(l == NULL){} else {close lseg(l,0,p,_);}*/}
  }
  //@if(l == NULL && head0 != r){open lseg(l,0,_);}
  //@lseg_append_final(head0);
  //@if(head0 == r){open lseg(head0,r,_);}
  //@assert true;
}



/*---------------------------------------------------------------------------*/
/**
 * Get the length of a list.
 *
 * This function counts the number of elements on a specified list.
 *
 * \param list The list.
 * \return The length of the list.
 */
/*---------------------------------------------------------------------------*/
int list_length(list_t list)
//@requires true &*& pointer(list,?head) &*& lseg(head,0,_);
//@ensures true &*& pointer(list,head) &*& lseg(head,0,_);
{
  struct list *l;
  int n = 0;

  for(l = *list; l != NULL; ) 
  //@requires lseg(head,l,_) &*& lseg(l,0,_);
  //@ensures lseg(head,l,_) &*& lseg(l,0,_);
  {
   	 ++n;
   	 //@struct list* temp = l;
	 l = l->next;
	 //@close lseg(l,l,_);
	 //@open lseg(l,0,_);
	 //@close lseg(temp,l,_);
	 //@close lseg(l,0,_);
	 //@lseg_append(head);
  }
  return n;
}
/*---------------------------------------------------------------------------*/
/**
 * \brief      Insert an item after a specified item on the list
 * \param list The list
 * \param previtem The item after which the new item should be inserted
 * \param newitem  The new item that is to be inserted
 * \author     Adam Dunkels
 *
 *             This function inserts an item right after a specified
 *             item on the list. This function is useful when using
 *             the list module to ordered lists.
 *
 *             If previtem is NULL, the new item is placed at the
 *             start of the list.
 *
 */
void list_insert(list_t list, void *previtem, void *newitem)
//@requires true &*& pointer(list, ?head) &*& lseg(head,previtem,_) &*& lseg(previtem,0,_) &*& lseg(newitem,0,1) &*& newitem != NULL;
//@ensures pointer(list,?head1) &*& lseg(head1,0,_);
{
  if(previtem == NULL) {
    list_push(list, newitem);
  } else 
  {
    //@struct list* temp = ((struct list *)newitem)->next;
    ((struct list *)newitem)->next = ((struct list *)previtem)->next;
    //@leak lseg(temp,0,_);
    ((struct list *)previtem)->next = newitem;
    //@lseg_append_final(head);
  }
  
}
/*---------------------------------------------------------------------------*/
/**
 * \brief      Get the next item following this item
 * \param item A list item
 * \returns    A next item on the list
 *
 *             This function takes a list item and returns the next
 *             item on the list, or NULL if there are no more items on
 *             the list. This function is used when iterating through
 *             lists.
 */
void *list_item_next(void *item)
//@requires  lseg(item,0,_);
//@ensures lseg(item,0,_);
{
  if(item == NULL)
  	return NULL;
  else
  {
  	return ((struct list *)item)->next;
  }
  //return item == NULL? NULL: ((struct list *)item)->next;
}
/*---------------------------------------------------------------------------*/
/** @} */
