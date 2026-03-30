/* Lock-based threads library specified and verified by Mansky et al.
   using the Verified Software Toolchain */

#ifndef _VST_THREADS_H_
#define _VST_THREADS_H_

typedef struct atom_int *lock_t;

lock_t makelock(void);

void freelock(lock_t lock);

void acquire(lock_t lock);

void release(lock_t lock);

int spawn(int (*f)(void*), void* args);

void join_thread(int tid);

#endif
