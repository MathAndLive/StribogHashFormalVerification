typedef unsigned long __u64;
typedef __u64 __le64;

struct streebog_uint512 {
	__le64 qword[8];
};

void streebog_xor(const struct streebog_uint512 *x,
			 const struct streebog_uint512 *y,
			 struct streebog_uint512 *z)
{
	z->qword[0] = x->qword[0] ^ y->qword[0];
	z->qword[1] = x->qword[1] ^ y->qword[1];
	z->qword[2] = x->qword[2] ^ y->qword[2];
	z->qword[3] = x->qword[3] ^ y->qword[3];
	z->qword[4] = x->qword[4] ^ y->qword[4];
	z->qword[5] = x->qword[5] ^ y->qword[5];
	z->qword[6] = x->qword[6] ^ y->qword[6];
	z->qword[7] = x->qword[7] ^ y->qword[7];
}

// int main() {
//   const struct streebog_uint512 *x;
//   const struct streebog_uint512 *y;
// 	struct streebog_uint512 *z;
//   streebog_xor(x, y, z);
// }
