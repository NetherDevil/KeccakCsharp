using System;
using System.Security.Cryptography;

namespace Keccak {
    internal class KeccakCore {
        byte[] state = new byte[200];
        int rateInBytes;
        int bytesPushed;
        byte suffix;
        int outLength;
        public KeccakCore(int rate, int capacity, byte delimitedSuffix, int outputLength) {
            if (rate + capacity != 1600 || rate % 8 != 0) { // Necessary checks.
                throw new ArgumentException("Invalid initializer arguments.");
            }
            rateInBytes = rate >> 3;
            suffix = delimitedSuffix;
            outLength = outputLength;
        }
        public void Initialize() {
            for (int i = 0; i < 200; i++) { // Initialize state.
                state[i] = 0;
            }
            bytesPushed = 0;
        }

        private bool LFSR86540(ref byte LFSR)
        {
            bool result = ((LFSR) & 0x01) != 0;
            if ((LFSR & 0x80) != 0) { // Primitive polynomial over GF(2): x^8+x^6+x^5+x^4+1
                LFSR = (byte)((LFSR << 1) ^ 0x71);
            }
            else {
                LFSR <<= 1;
            }
            return result;
        }

        private ulong LoadLane(int x, int y) {
            int startPos = (x + 5 * y) << 3;
            return 
                (((ulong)state[startPos + 0]) << 0) |
                (((ulong)state[startPos + 1]) << 8) |
                (((ulong)state[startPos + 2]) << 16) |
                (((ulong)state[startPos + 3]) << 24) |
                (((ulong)state[startPos + 4]) << 32) |
                (((ulong)state[startPos + 5]) << 40) |
                (((ulong)state[startPos + 6]) << 48) |
                (((ulong)state[startPos + 7]) << 56);
        }
        private void SaveLane(int x, int y, ulong lane) {
            int startPos = (x + 5 * y) << 3;
            state[startPos + 0] = (byte)((lane >> 0) & 0xFF);
            state[startPos + 1] = (byte)((lane >> 8) & 0xFF);
            state[startPos + 2] = (byte)((lane >> 16) & 0xFF);
            state[startPos + 3] = (byte)((lane >> 24) & 0xFF);
            state[startPos + 4] = (byte)((lane >> 32) & 0xFF);
            state[startPos + 5] = (byte)((lane >> 40) & 0xFF);
            state[startPos + 6] = (byte)((lane >> 48) & 0xFF);
            state[startPos + 7] = (byte)((lane >> 56) & 0xFF);
        }
        private void XorLane(int x, int y, ulong lane) {
            int startPos = (x + 5 * y) << 3;
            state[startPos + 0] ^= (byte)((lane >> 0) & 0xFF);
            state[startPos + 1] ^= (byte)((lane >> 8) & 0xFF);
            state[startPos + 2] ^= (byte)((lane >> 16) & 0xFF);
            state[startPos + 3] ^= (byte)((lane >> 24) & 0xFF);
            state[startPos + 4] ^= (byte)((lane >> 32) & 0xFF);
            state[startPos + 5] ^= (byte)((lane >> 40) & 0xFF);
            state[startPos + 6] ^= (byte)((lane >> 48) & 0xFF);
            state[startPos + 7] ^= (byte)((lane >> 56) & 0xFF);
        }
        private ulong XorShiftROL(ulong x, int offset) {
            return ((x << offset) | (x >> (64 - offset)));
        }

        private void StatePermute() {
            byte LFSRState = 0x01;
            ulong[] C = new ulong[5];
            ulong[] tmpx = new ulong[5];
            for (int i = 0; i < 24; i++) {
                // θ
                ulong D;
                for (int x = 0; x < 5; x++) { // Compute the parity of the columns
                    C[x] = LoadLane(x, 0) ^ LoadLane(x, 1) ^ LoadLane(x, 2) ^ LoadLane(x, 3) ^ LoadLane(x, 4);
                }
                for (int x = 0; x < 5; x++) { // Compute the parity of the columns
                    D = C[(x + 4) % 5] ^ XorShiftROL(C[(x + 1) % 5], 1); // Compute the θ effect for a given column
                    XorLane(x, 0, D); // Add the θ effect to the whole column
                    XorLane(x, 1, D);
                    XorLane(x, 2, D);
                    XorLane(x, 3, D);
                    XorLane(x, 4, D);
                }

                // ρ & π
                ulong current, temp;
                int tx = 1, ty = 0; // Start at coordinates (1, 0)
                current = LoadLane(tx, ty); 
                for(int t = 0; t < 24; t++) { // Iterate over ((0, 1) (2, 3)) ^ t * (1, 0) for 0 <= t <= 23
                    int r = ((t + 1) * (t + 2) / 2) % 64; // Compute the rotation constant r = (t + 1)(t + 2)/2
                    int Y = (2 * tx + 3 * ty) % 5; tx = ty; ty = Y; // Compute ((0, 1) (2, 3)) * (tx, ty)
                    temp = LoadLane(tx, ty); // Swap current and state(x,y), and rotate 
                    SaveLane(tx, ty, XorShiftROL(current, r));
                    current = temp;
                }

                // χ
                for(int y = 0; y < 5; y++) {
                    for(int x = 0; x < 5; x++) { // Take a copy of the plane 
                        tmpx[x] = LoadLane(x, y);
                    }
                    for(int x = 0; x < 5; x++) { // Compute χ on the plane
                        SaveLane(x, y, tmpx[x] ^ ((~tmpx[(x + 1) % 5]) & tmpx[(x + 2) % 5]));
                    }
                }

                // ι
                for(int j = 0; j < 7; j++) {
                    int bitPosition = (1 << j) - 1; // 2 ^ j - 1
                    if (LFSR86540(ref LFSRState))
                        XorLane(0, 0, 1ul << bitPosition);
                }
            }
        }
        private void PushByte(byte b) {
            state[bytesPushed++] ^= b;
            if (bytesPushed == rateInBytes) {
                StatePermute();
                bytesPushed = 0;
            }
        }

        public void HashCore(byte[] array, int ibStart, int cbSize) {
            for (int i = 0; i < cbSize; i++) {
                PushByte(array[ibStart + i]);
            }
        }

        public byte[] HashFinal() {
            state[bytesPushed] ^= suffix;
            if (((suffix & 0x80) != 0) && (bytesPushed == (rateInBytes - 1))) {
                StatePermute();
            }
            state[rateInBytes - 1] ^= 0x80;
            StatePermute();
            byte[] result = new byte[outLength];
            int outputByteLen = outLength, offset = 0;
            while(outputByteLen > 0) {
                int blockSize = int.Min(outputByteLen, rateInBytes);
                for (int i = 0; i < blockSize; i++) {
                    result[i + offset] = state[i];
                }
                offset += blockSize;
                outputByteLen -= blockSize;
                if (outputByteLen > 0) {
                    StatePermute();
                }
            }
            return result;
        }
    }

    public class SHA3_224 : HashAlgorithm {
        KeccakCore keccak;
        public SHA3_224() { keccak = new KeccakCore(1152, 448, 0x06, 28); }
        public override void Initialize() { keccak.Initialize(); }
        protected override void HashCore(byte[] array, int ibStart, int cbSize) { keccak.HashCore(array, ibStart, cbSize); }
        protected override byte[] HashFinal() { return keccak.HashFinal(); }
    }
    public class SHA3_256 : HashAlgorithm {
        KeccakCore keccak;
        public SHA3_256() { keccak = new KeccakCore(1088, 512, 0x06, 32); }
        public override void Initialize() { keccak.Initialize(); }
        protected override void HashCore(byte[] array, int ibStart, int cbSize) { keccak.HashCore(array, ibStart, cbSize); }
        protected override byte[] HashFinal() { return keccak.HashFinal(); }
    }
    public class SHA3_384 : HashAlgorithm {
        KeccakCore keccak;
        public SHA3_384() { keccak = new KeccakCore(832, 768, 0x06, 48); }
        public override void Initialize() { keccak.Initialize(); }
        protected override void HashCore(byte[] array, int ibStart, int cbSize) { keccak.HashCore(array, ibStart, cbSize); }
        protected override byte[] HashFinal() { return keccak.HashFinal(); }
    }
    public class SHA3_512 : HashAlgorithm {
        KeccakCore keccak;
        public SHA3_512() { keccak = new KeccakCore(576, 1024, 0x06, 64); }
        public override void Initialize() { keccak.Initialize(); }
        protected override void HashCore(byte[] array, int ibStart, int cbSize) { keccak.HashCore(array, ibStart, cbSize); }
        protected override byte[] HashFinal() { return keccak.HashFinal(); }
    }
}