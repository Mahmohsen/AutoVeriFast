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
 * Author: Adam Dunkels <adam@sics.se>
 *
 */

/**
 * \addtogroup memb
 * @{
 */

 /**
 * \file
 * Memory block allocation routines.
 * \author Adam Dunkels <adam@sics.se>
 */
#include <string.h>
#include "stdlib.h"

//#include "contiki/contiki.h"
//#include "memb.h"

//The following predicates are auto generated 
/*@
  predicate memb(struct memb* memb;) = memb->size |-> ?size &*& memb->num |-> ?num &*& memb->count |-> ?count1 &*& memb->mem |-> ?mem &*& chars(count1, num ,?cs) &*& chars(mem, (unsigned short) (size * num), ?cs1) &*& malloc_block_memb(memb);
@*/




struct memb {  unsigned short size;  unsigned short num;  char *count;
  void *mem;
};



/*---------------------------------------------------------------------------*/
void memb_init(struct memb *m)
//@requires true;
//@ensures true;
{
  memset(m->count, 0, m->num);
  memset(m->mem, 0, (unsigned short) (m->size * m->num));
}
/*---------------------------------------------------------------------------*/
void *memb_alloc(struct memb *m)
//@requires true;
//@ensures true;
{
  int i;

  for(i = 0; i < m->num; ++i) 
  //@requires true;
  //@ensures true;
  {   
    if(m->count[i] == 0) {
      /* If this block was unused, we increase the reference count to
	 indicate that it now is used and return a pointer to the
	 memory block. */
      ++(m->count[i]);
      abort();
      
    }
  }
  if(i < m->num)
   return (void *)((char *)m->mem + (i * m->size));
  
  /* No free block was found, so we return NULL to indicate failure to
     allocate block. */
  else
  {
   
   return NULL;
  
  }


}/*---------------------------------------------------------------------------*/
char memb_free(struct memb *m, void *ptr)
//@requires true;
//@ensures true;
{
  int i;
  char *ptr2;

  /* Walk through the list of blocks and try to find the block to
     which the pointer "ptr" points to. */
  ptr2 = (char *)m->mem;
  for(i = 0; i < m->num; ++i) 
  //@requires true;
  //@ensures true;
  {
    
    if(ptr2 == (char *)ptr) {
      /* We've found to block to which "ptr" points so we decrease the
	 reference count and return the new value of it. */
      if(m->count[i] > 0) {
	/* Make sure that we don't deallocate free memory. */
	--(m->count[i]);
      }
      abort();
      
    }
    ptr2 += m->size;
  }
  if(i < m->num) return m->count[i];
  else return -1;
}
/*---------------------------------------------------------------------------*/
int memb_inmemb(struct memb *m, void *ptr)
//@requires true;
//@ensures true;
{
	bool x = (char *)ptr >= (char *)m->mem &&
    (char *)ptr < (char *)m->mem + (m->num * m->size);
  int y;
  if(x == false) 
  	y = 0; 
  else y = 1;
  return y;
}
/*---------------------------------------------------------------------------*/
int memb_numfree(struct memb *m)
//@requires true;
//@ensures true;
{
  int i;
  int num_free = 0;

  for(i = 0; i < m->num; ++i) 
  //@requires true;
  //@ensures true;
  {
    if(m->count[i] == 0) {
      ++num_free;
    }
  }

  return num_free;
}
/** @} */