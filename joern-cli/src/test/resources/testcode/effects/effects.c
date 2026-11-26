void touch(int value);
void use(int value);

void caller(int a) {
  int x = a;
  touch(x);
  use(x);
}
