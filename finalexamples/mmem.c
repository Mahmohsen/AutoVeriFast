/*
 * Copyright (c) 2005, Swedish Institute of Computer Science
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
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
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
 */

/**
 * \addtogroup mmem
 * @{
 */

/**
 * \file
 *         Implementation of the managed memory allocator
 * \author
 *         Adam Dunkels <adam@sics.se>
 * 
 */


#include "mmem.h"
#include "list.h"
//#include "contiki-conf.h"
#include <string.h>

#ifdef MMEM_CONF_SIZE
#define MMEM_SIZE MMEM_CONF_SIZE
#else
#define MMEM_SIZE 4096
#endif

LIST(mmemlist);
unsigned int avail_memory;
static char memory[MMEM_SIZE];
static int inited = 0;


/*---------------------------------------------------------------------------*/
/**
 * \brief      Allocate a managed memory block
 * \param m    A pointer to a struct mmem.
 * \param size The size of the requested memory block
 * \return     Non-zero if the memory could be allocated, zero if memory
 *             was not available.
 * \author     Adam Dunkels
 *
 *             This function allocates a chunk of managed memory. The
 *             memory allocated with this function must be deallocated
 *             using the mmem_free() function.
 *
 *             \note This function does NOT return a pointer to the
 *             allocated memory, but a pointer to a structure that
 *             contains information about the managed memory. The
 *             macro MMEM_PTR() is used to get a pointer to the
 *             allocated memory.
 *
 */
 
int mmem_alloc(struct mmem *m, unsigned int size)
//@requires m->size |-> ?size1 &*& m->ptr |-> ?ptr &*& pointer(&mmemlist,?list) &*& pointer(list,?head) &*& lseg(head,0,_) &*& lseg((void*) m,0,1) &*& u_integer(&avail_memory,?avail_mem) &*& m != 0 &*& chars(memory,MMEM_SIZE,?cs) &*& avail_mem <= MMEM_SIZE &*& MMEM_SIZE - avail_mem >= 0 &*& MMEM_SIZE - avail_mem < MMEM_SIZE;
//@ensures m->size |-> ?size2 &*& m->ptr |-> ?ptr1 &*& pointer(&mmemlist,list) &*& pointer(list,?head1) &*& lseg(head1,0,_) &*&  u_integer(&avail_memory,_) &*& chars(memory,MMEM_SIZE,cs) &*& (avail_mem < size ? lseg((void*) m,0,1) : true) &*& avail_mem <= MMEM_SIZE &*& MMEM_SIZE - avail_mem >= 0 &*& MMEM_SIZE - avail_mem < MMEM_SIZE;
{
 // //@int y = (int) (MMEM_SIZE - avail_memory);
//  //@split
 // char x = memory[/*The explicit casting added by me Mahmoud*/(int)(MMEM_SIZE - avail_memory)];
 // char f = memory[MMEM_SIZE];
  /* Check if we have enough memory left for this allocation. */
  if(avail_memory < size) {
    return 0;
  }

  /* We had enough memory so we add this memory block to the end of
     the list of allocated memory blocks. */
  ////@assert pointer(head,?next);
  list_add(mmemlist, m);

  /* Set up the pointer so that it points to the first available byte
     in the memory block. */
  ////@open mmem(m);
 // //@open mmem(m);
 // //@open chars(m->ptr,_,_);
  m->ptr = (char*) memory + (int) (MMEM_SIZE - avail_memory); //&memory[MMEM_SIZE - avail_memory];;
  
  /* Remember the size of this memory block. */
  m->size = size;

  /* Decrease the amount of available memory. */
  avail_memory -= size;

  /* Return non-zero to indicate that we were able to allocate
     memory. */

  return 1;
}

/*@
//lemma void chars_split1(char *array, void *ptr, int x)
//	requires chars(array,x,?cs) &*& x >= 0 &*& x <MMEM_SIZE;
//	ensures  array == ptr ? chars(array, x, cs) : chars(array,?n1,?cs1) &*& chars(ptr,?n2,?cs2) &*& x >= 0 &*& x <MMEM_SIZE;
//{
//	if(array == ptr)
//	{
//	}
//	else
//	{
//		char y = array[x];
//		chars_split1(&y,ptr,x+1);
//	}	
//}

@*/
/*---------------------------------------------------------------------------*/
/**
 * \brief      Deallocate a managed memory block
 * \param m    A pointer to the managed memory block
 * \author     Adam Dunkels
 *
 *             This function deallocates a managed memory block that
 *             previously has been allocated with mmem_alloc().
 *
 */
 
/*@
lemma_auto void chars_split1(char *array, void* ptr);
   requires [?f]chars(array, ?n, ?cs) &*& ptr >= array &*& u_integer(&avail_memory,?avail_mem);
   ensures
       [f]chars(array, (char*) ptr - array, _)
       &*& [f]chars(ptr, (array + (n - avail_mem)) - (char*) ptr, _) &*& u_integer(&avail_memory,avail_mem);
       
@*/ 
 
 
void mmem_free(struct mmem *m)
//@requires m->ptr |-> ?ptr  &*& m->next |-> ?next &*& next->ptr |-> ?nptr &*& next->next |-> ?nnext &*& pointer(&mmemlist,?list) &*& pointer(list,?head) &*& lseg(head,0,_) &*& u_integer(&avail_memory,?avail_mem) &*& chars(memory,MMEM_SIZE,?cs) &*& avail_mem <= MMEM_SIZE &*& MMEM_SIZE - avail_mem >= 0 &*& MMEM_SIZE - avail_mem < MMEM_SIZE &*&  ptr < ((char*) memory + MMEM_SIZE) &*& ptr > (char*) memory &*& nptr < ((char*) memory + MMEM_SIZE) &*& nptr > (char*) memory;
//@ensures m->ptr |-> ptr &*& m->next |-> next &*& mmem(next) &*& pointer(&mmemlist,list) &*& pointer(list,?head1) &*& lseg(head1,0,_) &*& u_integer(&avail_memory,?avail_mem1) &*& chars(memory,MMEM_SIZE,cs);
{
  char x = memory[/*The explicit casting added by me Mahmoud*/(int)(MMEM_SIZE - avail_memory)];
  struct mmem *n;
  
  //@chars_split1(memory,nptr);
  //@if(ptr <= nptr){chars_split1(memory,nptr);} else {chars_split1(memory, nptr + (unsigned int) ((char*) memory + (int) (MMEM_SIZE - avail_memory)));}
  if(m->next != NULL) {
    memmove(m->ptr, m->next->ptr,
	    (unsigned int) ((char*) memory + (int) (MMEM_SIZE - avail_memory)) - (unsigned int)(char *)m->next->ptr);

	        
    /* Update all the memory pointers that points to memory that is
       after the allocation that is to be removed. */
    for(n = m->next; n != NULL; n = n->next) 
    //@requires m->size |-> ?size &*& mmem(n) ;
    //@ensures m->size |-> size &*& mmem(old_n);
    {
      n->ptr = (void *)((char *)n->ptr - (int)(m->size));
    }
  }

  avail_memory += m->size;

  /* Remove the memory block from the list. */
  list_remove(mmemlist, m);
}
/*---------------------------------------------------------------------------*/
/**
 * \brief      Initialize the managed memory module
 * \author     Adam Dunkels
 *
 *             This function initializes the managed memory module and
 *             should be called before any other function from the
 *             module.
 *
 */
void mmem_init(void)
//@requires true &*& integer(&inited, ?init) &*& (init == 1 ? true : pointer(&mmemlist,?list) &*& pointer(list, ?head0) &*& u_integer(&avail_memory,?avail_mem));
//@ensures true &*& integer(&inited,?init1) &*& (init == 1 ? true : pointer(&mmemlist, ?list1) &*& pointer(list1,?head1) &*& u_integer(&avail_memory,?avail_mem1));
{
  if(inited) {
    return;
  }
  list_init(mmemlist);
  avail_memory = MMEM_SIZE;
  inited = 1;
}
/*---------------------------------------------------------------------------*/

/** @} */
