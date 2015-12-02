#pragma once

#include <acpi.h>

struct Atable *acpihpet(char *name, uint8_t *p, size_t rawsize);
