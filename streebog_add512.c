typedef unsigned long __u64;
typedef __u64 __le64;

struct streebog_uint512 {
	__le64 qword[8];
};

#define le64_to_cpu
#define cpu_to_le64

typedef unsigned long long u64;

void streebog_add512(const struct streebog_uint512 *x,
			    const struct streebog_uint512 *y,
			    struct streebog_uint512 *r)
{
	u64 carry = 0;
	int i;

	for (i = 0; i < 8; i++) {
		const u64 left = le64_to_cpu(x->qword[i]);
		u64 sum;

		sum = left + le64_to_cpu(y->qword[i]) + carry;
		if (sum != left)
			carry = (sum < left);
		r->qword[i] = cpu_to_le64(sum);
	}
}
