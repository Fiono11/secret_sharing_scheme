# secret_sharing_scheme
Implementation of a verifiable weighted threshold secret sharing scheme

This implementation is based on the following papers:
- ["Constructing Ideal Secret Sharing Schemes based on Chinese Remainder Theorem"](https://eprint.iacr.org/2018/837.pdf) for the weighted threshold secret sharing scheme;
- ["Zexe: Enabling Decentralized Private Computation"](https://eprint.iacr.org/2018/962.pdf) for making the scheme verifiable through a polynomial commitment scheme;
- ["A tool for implementing privacy in Nano"](https://ubibliorum.ubi.pt/bitstream/10400.6/7645/1/1570608765.pdf) for the decryption without reconstructing the secret (TODO).

**WARNING**: This is an academic proof-of-concept prototype, and in particular has not received careful code review. This implementation is NOT ready for production use.
