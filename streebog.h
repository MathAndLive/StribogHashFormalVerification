/* SPDX-License-Identifier: GPL-2.0+ OR BSD-2-Clause */
/*
 * Copyright (c) 2013 Alexey Degtyarev <alexey@renatasystems.org>
 * Copyright (c) 2018 Vitaly Chikunov <vt@altlinux.org>
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 2 of the License, or (at your option)
 * any later version.
 */

#ifndef _CRYPTO_STREEBOG_H_
#define _CRYPTO_STREEBOG_H_

//#include <linux/types.h> // __u64 и __le64
typedef unsigned long long __le64;

#define STREEBOG256_DIGEST_SIZE	32
#define STREEBOG512_DIGEST_SIZE	64
#define STREEBOG_BLOCK_SIZE	64

// необходимо будет прописать тройки Хоара для них так, что вход равен выходу
// оставляем так в предположении того, что работаем с little-endian машиной
#define cpu_to_le64 
#define le64_to_cpu

typedef unsigned char u8; /* source: https://elixir.bootlin.com/linux/v6.15.6/source/arch/powerpc/boot/types.h#L12 */
typedef unsigned int u32; /* source: https://elixir.bootlin.com/linux/v6.15.6/source/arch/powerpc/boot/types.h#L12 */
typedef unsigned long long u64; /* source: https://elixir.bootlin.com/linux/v6.15.6/source/arch/powerpc/boot/types.h#L12 */

/* // для справки, надо прописать в предусловиях
static inline void *shash_desc_ctx(struct shash_desc *desc)
{
	return desc->__ctx;
}
*/ 

/* // в предусловиях пропишем, что это либо STREEBOG256_DIGEST_SIZE, либо STREEBOG512_DIGEST_SIZE
static inline unsigned int crypto_shash_digestsize(struct crypto_shash *tfm)
{
	return crypto_shash_alg(tfm)->digestsize;
}
*/

struct shash_desc {
	struct crypto_shash *tfm;
	void * __ctx[]; // __aligned(ARCH_SLAB_MINALIGN); // несущественное
};

typedef long unsigned int size_t;

// для этих трёх функций стоит поискать спецификацию в VST и CompCert

void *memcpy(void *dest, const void *src, size_t count);

void *memset(void *s, int c, size_t count);

static inline void memzero_explicit(void *s, size_t count);

struct streebog_uint512 { // 8 64-bit little endian blocks comprising a 512 bit unsigned integer
	__le64 qword[8];
};

struct streebog_state {
	struct streebog_uint512 hash;
	struct streebog_uint512 h;
	struct streebog_uint512 N;
	struct streebog_uint512 Sigma;
};

#endif /* !_CRYPTO_STREEBOG_H_ */
