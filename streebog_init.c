#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#define STREEBOG256_DIGEST_SIZE	64 // Договорились, что размер хеша для Streebog будет 64 байта
#define ARCH_SLAB_MINALIGN	16 // Минимальный выравнивание для слэба, например, 16 байт для x86_64

#define cpu_to_le64(x) (x) 
#define crypto_shash_digestsize(tfm) STREEBOG256_DIGEST_SIZE

#define __aligned(x) __attribute__((aligned(x))) // Макрос для выравнивания структуры

#include "streebog.h"

struct shash_desc {
	struct crypto_shash *tfm;  // Указатель на алгоритм (struct crypto_shash), например, "streebog256".
	void *__ctx[] __aligned(ARCH_SLAB_MINALIGN); // Массив байт произвольного размера, для хранения внутреннего состояния (конкретной реализации SHA, Streebog и т.п.).
};


static inline void *shash_desc_ctx(struct shash_desc *desc)
{
	return desc->__ctx;
}


static int streebog_init(struct shash_desc *desc)
{
	struct streebog_state *ctx = shash_desc_ctx(desc); // Получаем указатель на внутреннее состояние контекста хеширования
	unsigned int digest_size = crypto_shash_digestsize(desc->tfm); // Получаем размер хеша из структуры алгоритма
	unsigned int i; 

	memset(ctx, 0, sizeof(struct streebog_state)); 
	for (i = 0; i < 8; i++) {
		if (digest_size == STREEBOG256_DIGEST_SIZE)
			ctx->h.qword[i] = cpu_to_le64(0x0101010101010101ULL);
	}
	return 0;
}

int main() {

    struct shash_desc *desc = malloc(sizeof(struct shash_desc) + sizeof(struct streebog_state));
    if (!desc) {
        fprintf(stderr, "Failed to allocate memory for shash_desc\n");
        return 1;
    }

    desc->tfm = NULL;

    int result = streebog_init(desc);
    if (result == 0) {
        printf("Streebog initialization successful.\n");

        struct streebog_state *ctx = shash_desc_ctx(desc);
        printf("Initialized state:\n");
        for (int i = 0; i < 8; i++) {
            printf("ctx->h.qword[%d] = 0x%016llx\n", i, ctx->h.qword[i]);
        }
    } else {
        fprintf(stderr, "Streebog initialization failed.\n");
    }

    free(desc);

    return 0;
}