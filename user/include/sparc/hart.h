#ifndef PARLIB_ARCH_HART_H
#define PARLIB_ARCH_HART_H

#include <ros/common.h>
#include <ros/arch/trapframe.h>

/* Pops an ROS kernel-provided TF, reanabling notifications at the same time.
 * A Userspace scheduler can call this when transitioning off the transition
 * stack.
 *
 * Here's how x86 does it:
 * Basically, it sets up the future stack pointer to have extra stuff after it,
 * and then it pops the registers, then pops the new context's stack
 * pointer.  Then it uses the extra stuff (the new PC is on the stack, the
 * location of notif_enabled, and a clobbered work register) to enable notifs,
 * restore the work reg, and then "ret".
 *
 * The important thing is that it can a notification after it enables
 * notifications, and when it gets resumed it can ultimately run the new
 * context.  Enough state is saved in the running context and stack to continue
 * running. */
static inline void pop_ros_tf(struct user_trapframe *tf, bool *notif_en_loc)
{
	// TODO: whatever sparc needs.
}

/* Feel free to ignore vcoreid.  It helps x86 to avoid a call to
 * sys_getvcoreid() if we pass it in. */
static inline void *get_tls_desc(uint32_t vcoreid)
{
	void *tmp;
	asm volatile ("mov %%g7,%0" : "=r"(tmp));
	return tmp;
}

static inline void set_tls_desc(void *tls_desc, uint32_t vcoreid)
{
	asm volatile ("mov %0,%%g7" : : "r"(tls_desc) : "memory");
}
#endif /* PARLIB_ARCH_HART_H */
