static const struct streebog_uint512 buffer0;
static const struct streebog_uint512 buffer512;
static const struct streebog_uint512 C[12];
static const unsigned long long Ax[8][256];	

static void streebog_xor;
static void streebog_xlps;
static void streebog_round;
static int streebog_init;
static void streebog_add512;
static void streebog_g;
static void streebog_stage2;
static void streebog_stage3;
static int streebog_update;
static int streebog_finup;

static struct shash_alg algs[2];

static int __init streebog_mod_init(void);
static void __exit streebog_mod_fini(void);
