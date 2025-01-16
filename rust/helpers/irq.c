// SPDX-License-Identifier: GPL-2.0
#include <linux/irqchip/chained_irq.h>
#include <linux/irqdomain.h>
#include <linux/irq.h>

void rust_helper_irq_set_handler_locked(struct irq_data *data,
					irq_flow_handler_t handler)
{
	irq_set_handler_locked(data, handler);
}

void *rust_helper_irq_data_get_irq_chip_data(struct irq_data *d)
{
	return irq_data_get_irq_chip_data(d);
}

struct irq_chip *rust_helper_irq_desc_get_chip(struct irq_desc *desc)
{
	return irq_desc_get_chip(desc);
}

void *rust_helper_irq_desc_get_handler_data(struct irq_desc *desc)
{
	return irq_desc_get_handler_data(desc);
}

void rust_helper_chained_irq_enter(struct irq_chip *chip,
				   struct irq_desc *desc)
{
	chained_irq_enter(chip, desc);
}

void rust_helper_chained_irq_exit(struct irq_chip *chip,
				   struct irq_desc *desc)
{
	chained_irq_exit(chip, desc);
}