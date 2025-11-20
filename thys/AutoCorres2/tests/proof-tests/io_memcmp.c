/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned int do_memcmp (unsigned char *p1, unsigned int l1, unsigned char *p2, unsigned int l2)
{
	unsigned int i;
	if (l1 == 0)
		return 0;
	if (l1 != l2)
		return 0;
	if (p1 == 0)
		return 0;
	if (p2 == 0)
		return 0;
	for (i = 0; i < l1; i++)
		if (p1[i] != p2[i])
			return 0;
	return -1;
}

unsigned int main1(unsigned char *vp, unsigned int lp)
{
	unsigned char *vl;
	unsigned int ll;
	static unsigned char bg;
	unsigned int r;

	r = do_memcmp (vp, lp, vl, ll);
	r = do_memcmp (&bg, sizeof(bg), vl, ll);
	return r;
}