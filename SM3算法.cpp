#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

// 常量定义
#define SM3_BLOCK_SIZE 64
#define SM3_DIGEST_SIZE 32

// 初始化向量
static const uint32_t IV[8] = {
    0x7380166F, 0x4914B2B9, 0x172442D7, 0xDA8A0600,
    0xA96F30BC, 0x163138AA, 0xE38DEE4D, 0xB0FB0E4E
};

// 循环左移
#define ROTL(x, n) (((x) << (n)) | ((x) >> (32 - (n))))

// 布尔函数
#define FF0(x, y, z) ((x) ^ (y) ^ (z))
#define FF1(x, y, z) (((x) & (y)) | (x) & (z) | (y) & (z))
#define GG0(x, y, z) ((x) ^ (y) ^ (z))
#define GG1(x, y, z) (((x) & (y)) | (~(x) & (z)))

// 置换函数
#define P0(x) ((x) ^ ROTL(x, 9) ^ ROTL(x, 17))
#define P1(x) ((x) ^ ROTL(x, 15) ^ ROTL(x, 23))

// 常量Tj
#define T(j) ((j) < 16 ? 0x79CC4519 : 0x7A879D8A)

// 消息扩展
static void message_extension(const uint32_t *B, uint32_t *W, uint32_t *W1) {
    int j;
    // 生成W[0..67]
    for (j = 0; j < 16; j++) {
        W[j] = B[j];
    }
    for (j = 16; j < 68; j++) {
        W[j] = P1(W[j-16] ^ W[j-9] ^ ROTL(W[j-3], 15)) ^ ROTL(W[j-13], 7) ^ W[j-6];
    }
    // 生成W1[0..63]
    for (j = 0; j < 64; j++) {
        W1[j] = W[j] ^ W[j+4];
    }
}

// 压缩函数
static void cf(uint32_t *V, const uint32_t *B) {
    uint32_t W[68], W1[64];
    uint32_t A, B_reg, C, D, E, F, G, H;
    uint32_t SS1, SS2, TT1, TT2;
    int j;

    // 消息扩展
    message_extension(B, W, W1);

    // 初始化工作变量
    A = V[0];
    B_reg = V[1];
    C = V[2];
    D = V[3];
    E = V[4];
    F = V[5];
    G = V[6];
    H = V[7];

    // 64轮迭代
    for (j = 0; j < 64; j++) {
        SS1 = ROTL((ROTL(A, 12) + E + ROTL(T(j), j)), 7);
        SS2 = SS1 ^ ROTL(A, 12);
        
        if (j < 16) {
            TT1 = FF0(A, B_reg, C) + D + SS2 + W1[j];
            TT2 = GG0(E, F, G) + H + SS1 + W[j];
        } else {
            TT1 = FF1(A, B_reg, C) + D + SS2 + W1[j];
            TT2 = GG1(E, F, G) + H + SS1 + W[j];
        }

        D = C;
        C = ROTL(B_reg, 9);
        B_reg = A;
        A = TT1;
        H = G;
        G = ROTL(F, 19);
        F = E;
        E = P0(TT2);
    }

    // 更新链接变量
    V[0] ^= A;
    V[1] ^= B_reg;
    V[2] ^= C;
    V[3] ^= D;
    V[4] ^= E;
    V[5] ^= F;
    V[6] ^= G;
    V[7] ^= H;
}

// 将字节转换为大端字
static void bytes_to_words(const uint8_t *bytes, uint32_t *words, int num_words) {
    int i;
    for (i = 0; i < num_words; i++) {
        words[i] = (uint32_t)bytes[4*i] << 24 |
                   (uint32_t)bytes[4*i + 1] << 16 |
                   (uint32_t)bytes[4*i + 2] << 8 |
                   (uint32_t)bytes[4*i + 3];
    }
}

// 将字转换为字节
static void words_to_bytes(const uint32_t *words, uint8_t *bytes, int num_words) {
    int i;
    for (i = 0; i < num_words; i++) {
        bytes[4*i] = (uint8_t)(words[i] >> 24);
        bytes[4*i + 1] = (uint8_t)(words[i] >> 16);
        bytes[4*i + 2] = (uint8_t)(words[i] >> 8);
        bytes[4*i + 3] = (uint8_t)words[i];
    }
}

// SM3主函数
void sm3_hash(const uint8_t *msg, size_t msg_len, uint8_t *digest) {
    uint32_t V[8];
    uint8_t block[SM3_BLOCK_SIZE];
    size_t remaining = msg_len;
    size_t i;

    // 初始化向量
    memcpy(V, IV, 8 * sizeof(uint32_t));

    // 处理完整的消息块
    while (remaining >= SM3_BLOCK_SIZE) {
        uint32_t B[16];
        bytes_to_words(msg, B, 16);
        cf(V, B);
        msg += SM3_BLOCK_SIZE;
        remaining -= SM3_BLOCK_SIZE;
    }

    // 处理剩余数据并填充
    memcpy(block, msg, remaining);
    block[remaining] = 0x80;  // 添加10000000

    // 如果剩余空间不足以存放长度信息(8字节)，则先处理当前块
    if (remaining + 1 > SM3_BLOCK_SIZE - 8) {
        memset(block + remaining + 1, 0, SM3_BLOCK_SIZE - remaining - 1);
        uint32_t B[16];
        bytes_to_words(block, B, 16);
        cf(V, B);
        memset(block, 0, SM3_BLOCK_SIZE);
    } else {
        memset(block + remaining + 1, 0, SM3_BLOCK_SIZE - remaining - 1 - 8);
    }

    // 添加长度信息(单位：比特)
    uint64_t bit_len = (uint64_t)msg_len * 8;
    for (i = 0; i < 8; i++) {
        block[SM3_BLOCK_SIZE - 8 + i] = (uint8_t)(bit_len >> (8 * (7 - i)));
    }

    // 处理最后一个块
    uint32_t B[16];
    bytes_to_words(block, B, 16);
    cf(V, B);

    // 输出结果
    words_to_bytes(V, digest, 8);
}

// 辅助函数：将哈希结果转换为十六进制字符串
void sm3_hex_digest(const uint8_t *digest, char *hex_str) {
    const char *hex_chars = "0123456789abcdef";
    for (int i = 0; i < SM3_DIGEST_SIZE; i++) {
        hex_str[2*i] = hex_chars[(digest[i] >> 4) & 0x0F];
        hex_str[2*i + 1] = hex_chars[digest[i] & 0x0F];
    }
    hex_str[2*SM3_DIGEST_SIZE] = '\0';
}

// 示例用法
int main() {
    // 测试向量1：空消息
    uint8_t digest1[SM3_DIGEST_SIZE];
    sm3_hash(NULL, 0, digest1);
    char hex1[2*SM3_DIGEST_SIZE + 1];
    sm3_hex_digest(digest1, hex1);
    printf("空消息哈希: %s\n", hex1);

    // 测试向量2："abc"
    const char *msg2 = "abc";
    uint8_t digest2[SM3_DIGEST_SIZE];
    sm3_hash((const uint8_t*)msg2, strlen(msg2), digest2);
    char hex2[2*SM3_DIGEST_SIZE + 1];
    sm3_hex_digest(digest2, hex2);
    printf("\"abc\"哈希: %s\n", hex2);

    return 0;
}

