// SPDX-License-Identifier: GPL-2.0

#include <linux/kernel.h>

void rust_helper_might_sleep(void)
{
	might_sleep();
}