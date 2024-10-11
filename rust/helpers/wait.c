// SPDX-License-Identifier: GPL-2.0

#include <linux/export.h>
#include <linux/wait.h>
#include <linux/sched.h>

void rust_helper_init_wait(struct wait_queue_entry *wq_entry)
{
	init_wait(wq_entry);
}

void rust_helper_init_waitqueue_head(struct wait_queue_head *wq_head)
{
	init_waitqueue_head(wq_head);
}

int rust_helper_wake_up(struct wait_queue_head *wq_head)
{
	return wake_up(wq_head);
}

int rust_helper_wake_up_interruptible(struct wait_queue_head *wq_head)
{
	return wake_up_interruptible(wq_head);
}

void rust_helper_wait_event(struct wait_queue_head *wq_head, bool condition)
{
	wait_event(*wq_head, condition);
}

void rust_helper_wait_event_interruptible(struct wait_queue_head *wq_head, bool condition)
{
	wait_event_interruptible(*wq_head, condition);
}