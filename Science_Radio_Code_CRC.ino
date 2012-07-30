// Radio and Sensor Code by Janez Stefulj & Kevin Glinka, End of 2011

#include <Wire.h>
#include <string.h>
#include <OneWire.h>
#include <util/crc16.h>

int32_t lat = 0, lon = 0, alt = 0;
uint8_t hour = 0, minute = 0, second = 0, lock = 0, sats = 0;
unsigned long startGPS = 0;
int GPSerrorM = 0, GPSerrorL = 0, GPSerrorP = 0, GPSerrorT = 0, count = 0, n, gpsstatus, lockcount = 0;
int navmode;
int error = 0;
char latitude[11];
char longitude[11];

int DS18B20_Pin = 2; // DS18B20 Signal Pin on digital 2
int HumPin = A7;
int BattPin = A1;
int LED_PIN = 6; // onboard LED
int RH;
float BitToVolt = 0.0025;  // 2.56/1024

uint8_t buf[70]; // GPS receive buffer 

char TemperatureString[50];
char PressureString[50];
char AltitudeString[50];
char DSTemperString[50];
char HumidityString[50];
char DewPointString[50];
char VoltageString[50];

//Temperature Chip I/0
OneWire ds(DS18B20_Pin); // on digital pin 2

void fmtDouble(double val, byte precision, char *buf, unsigned bufLen = 0xffff);
unsigned fmtUnsigned(unsigned long val, char *buf, unsigned bufLen = 0xffff, byte width = 0);
unsigned fmtUnsigned(unsigned long val, char *buf, unsigned bufLen, byte width)
{
  if(!buf || !bufLen)
  return(0);
  
  // produce the digit string (backwards in the digit buffer)
  char dbuf[10];
  unsigned idx = 0;
  while (idx < sizeof(dbuf))
  {
    dbuf[idx++] = (val % 10) + '0';
    if((val /= 10) == 0)
    break;
  }
  
  // copy the optional leading zeroes and digits to the target buffer
  unsigned len = 0;
  byte padding = (width > idx) ? width - idx : 0;
  char c = '0';
  while ((--bufLen > 0) && (idx || padding))
  {
    if(padding)
    padding--;
    else
    c = dbuf[--idx];
    *buf++ = c;
    len++;
  }
  
  // add the null termination
  *buf = '\0';
  return(len);
}
void fmtDouble(double val, byte precision, char *buf, unsigned bufLen)
{
  if(!buf || !bufLen)
  return;
  
  // limit the precision to the maximum allowed value
  const byte maxPrecision = 6;
  if (precision > maxPrecision)
  precision = maxPrecision;
  
  if(--bufLen > 0)
  {
    // check for a negative value
    if(val < 0.0)
    {
      val = -val;
      *buf = '-';
      bufLen--;
    }
    
    // compute the rounding factor and fractional multiplier
    double roundingFactor = 0.5;
    unsigned long mult = 1;
    for(byte i = 0; i < precision; i++)
    {
      roundingFactor /= 10.0;
      mult *= 10;
    }
    
    if(bufLen > 0)
    {
      // apply the rounding factor
      val += roundingFactor;
      
      // add the integral portion to the buffer
      unsigned len = fmtUnsigned((unsigned long)val, buf, bufLen);
      buf += len;
      bufLen -= len;
    }
    
    // handle the fractional portion
    
    if((precision > 0) && (bufLen > 0))
    {
      *buf++ = '.';
      if(--bufLen > 0)
      buf += fmtUnsigned((unsigned long)((val - (unsigned long)val) * mult), buf, bufLen, precision);
    }
  }
  // null-terminate the string
  *buf = '\0';
}

#define BMP085_ADDRESS 0x77 // I2C address of BMP085

int RADIO_SPACE_PIN = 4;
int RADIO_MARK_PIN = 5;
char DATASTRING[400];
char WAITSTRING[40];
char STARTSTRING[40];

const unsigned char OSS = 0;  // Oversampling Setting

// Calibration values
int ac1;
int ac2;
int ac3;
unsigned int ac4;
unsigned int ac5;
unsigned int ac6;
int b1;
int b2;
int mb;
int mc;
int md;

// b5 is calculated in bmp085GetTemperature(...), this variable is also used in bmp085GetPressure(...)
// so ...Temperature(...) must be called before ...Pressure(...).
long b5; 

// Stores all of the bmp085's calibration values into global variables
// Calibration values are required to calculate temp and pressure
// This function should be called at the beginning of the program
void bmp085Calibration()
{
  ac1 = bmp085ReadInt(0xAA);
  ac2 = bmp085ReadInt(0xAC);
  ac3 = bmp085ReadInt(0xAE);
  ac4 = bmp085ReadInt(0xB0);
  ac5 = bmp085ReadInt(0xB2);
  ac6 = bmp085ReadInt(0xB4);
  b1 = bmp085ReadInt(0xB6);
  b2 = bmp085ReadInt(0xB8);
  mb = bmp085ReadInt(0xBA);
  mc = bmp085ReadInt(0xBC);
  md = bmp085ReadInt(0xBE);
}

// Calculate temperature in deg C
float bmp085GetTemperature(unsigned int ut){
  long x1, x2;

  x1 = (((long)ut - (long)ac6)*(long)ac5) >> 15;
  x2 = ((long)mc << 11)/(x1 + md);
  b5 = x1 + x2;

  float temp = ((b5 + 8)>>4);
  temp = temp /10;

  return temp;
}

// Calculate pressure given up
// calibration values must be known
// b5 is also required so bmp085GetTemperature(...) must be called first.
// Value returned will be pressure in units of Pa.
long bmp085GetPressure(unsigned long up){
  long x1, x2, x3, b3, b6, p;
  unsigned long b4, b7;

  b6 = b5 - 4000;
  // Calculate B3
  x1 = (b2 * (b6 * b6)>>12)>>11;
  x2 = (ac2 * b6)>>11;
  x3 = x1 + x2;
  b3 = (((((long)ac1)*4 + x3)<<OSS) + 2)>>2;

  // Calculate B4
  x1 = (ac3 * b6)>>13;
  x2 = (b1 * ((b6 * b6)>>12))>>16;
  x3 = ((x1 + x2) + 2)>>2;
  b4 = (ac4 * (unsigned long)(x3 + 32768))>>15;

  b7 = ((unsigned long)(up - b3) * (50000>>OSS));
  if (b7 < 0x80000000)
    p = (b7<<1)/b4;
  else
    p = (b7/b4)<<1;

  x1 = (p>>8) * (p>>8);
  x1 = (x1 * 3038)>>16;
  x2 = (-7357 * p)>>16;
  p += (x1 + x2 + 3791)>>4;

  long temp = p;
  return temp;
}

// Read 1 byte from the BMP085 at 'address'
char bmp085Read(unsigned char address)
{
  unsigned char data;

  Wire.beginTransmission(BMP085_ADDRESS);
  Wire.write(address);
  Wire.endTransmission();

  Wire.requestFrom(BMP085_ADDRESS, 1);
  while(!Wire.available())
    ;

  return Wire.read();
}

// Read 2 bytes from the BMP085
// First byte will be from 'address'
// Second byte will be from 'address'+1
int bmp085ReadInt(unsigned char address)
{
  unsigned char msb, lsb;

  Wire.beginTransmission(BMP085_ADDRESS);
  Wire.write(address);
  Wire.endTransmission();

  Wire.requestFrom(BMP085_ADDRESS, 2);
  while(Wire.available()<2)
    ;
  msb = Wire.read();
  lsb = Wire.read();

  return (int) msb<<8 | lsb;
}

// Read the uncompensated temperature value
unsigned int bmp085ReadUT(){
  unsigned int ut;

  // Write 0x2E into Register 0xF4
  // This requests a temperature reading
  Wire.beginTransmission(BMP085_ADDRESS);
  Wire.write(0xF4);
  Wire.write(0x2E);
  Wire.endTransmission();

  // Wait at least 4.5ms
  delay(5);

  // Read two bytes from registers 0xF6 and 0xF7
  ut = bmp085ReadInt(0xF6);
  return ut;
}

// Read the uncompensated pressure value
unsigned long bmp085ReadUP(){

  unsigned char msb, lsb, xlsb;
  unsigned long up = 0;

  // Write 0x34+(OSS<<6) into register 0xF4
  // Request a pressure reading w/ oversampling setting
  Wire.beginTransmission(BMP085_ADDRESS);
  Wire.write(0xF4);
  Wire.write(0x34 + (OSS<<6));
  Wire.endTransmission();

  // Wait for conversion, delay time dependent on OSS
  delay(2 + (3<<OSS));

  // Read register 0xF6 (MSB), 0xF7 (LSB), and 0xF8 (XLSB)
  msb = bmp085Read(0xF6);
  lsb = bmp085Read(0xF7);
  xlsb = bmp085Read(0xF8);

  up = (((unsigned long) msb << 16) | ((unsigned long) lsb << 8) | (unsigned long) xlsb) >> (8-OSS);

  return up;
}

void writeRegister(int deviceAddress, byte address, byte val) {
  Wire.beginTransmission(deviceAddress); // start transmission to device 
  Wire.write(address);       // send register address
  Wire.write(val);         // send value to write
  Wire.endTransmission();     // end transmission
}

int readRegister(int deviceAddress, byte address){

  int v;
  Wire.beginTransmission(deviceAddress);
  Wire.write(address); // register to read
  Wire.endTransmission();

  Wire.requestFrom(deviceAddress, 1); // read a byte

  while(!Wire.available()) {
    // waiting
  }
  
  v = Wire.read();
  return v;
}

float calcAltitude(float pressure){

  float A = pressure/101325;
  float B = 1/5.25588;
  float C = pow(A,B);
  C = 1 - C;
  C = C /0.0000225577;

  return C;
}

void rtty_txstring(char * string)
{
  /* Simple function to send a char at a time to 
  rtty_txbyte function.
  NB each char is one byte (8 bits) */
  
  char c;
  
  c= *string++;
  
  while( c != '\0')
  {
    rtty_txbyte(c);
    c = *string++;
  }
}

void rtty_txbyte(char c)
{
  /* Simple function to send a each bit of a char to rtty_txbit function.
  
  NB The bits are sent Least Significant Bit first
  
  All chars should be preceded with a 0 and succeeded by a 1. 0 = start bit, 1 = stop bit */
  
  int i;
  
  rtty_txbit(0); // Start Bit
  
  // Send bits for char LSB first
  
  for(i=0;i<7;i++) // Change this here 7 or 8 for ASCII-7 / ASCII-8
  {
    if(c & 1) rtty_txbit(1);
    
    else rtty_txbit(0);
    
    c = c >> 1;
  }
  rtty_txbit(1); // Stop Bit
}

void rtty_txbit(int bit)
{
  if(bit)
  {
    // high
    digitalWrite(RADIO_MARK_PIN, HIGH);
    digitalWrite(RADIO_SPACE_PIN, LOW);
    digitalWrite(LED_PIN, HIGH);
  }
  else
  {
  // low
  digitalWrite(RADIO_MARK_PIN, LOW);
  digitalWrite(RADIO_SPACE_PIN, HIGH);
  digitalWrite(LED_PIN, LOW);
  }
  
//  delayMicroseconds(1680); // 600 Baud, unlikely to work
  delayMicroseconds(3370); // 300 Baud
//  delayMicroseconds(10000); // For 50 Baud uncommend this and the line below.
//  delayMicroseconds(10150); // For some reason you can't do 20150 it just doesn't work.
}

uint16_t crccat(char *msg)
{
	uint16_t x;
	for(x = 0xFFFF; *msg; msg++)
		x = _crc_xmodem_update(x, *msg);
	snprintf(msg, 8, "*%04X\n", x);
	return(x);
}

float getTemp(){
//returns the temperature from one DS18S20 in DEG Celsius

byte data[12];
byte addr[8];

if ( !ds.search(addr)) {
//no more sensors on chain, reset search
ds.reset_search();
return -1000;
}

if ( OneWire::crc8( addr, 7) != addr[7]) {
Serial.println("CRC is not valid!");
return -1000;
}

if ( addr[0] != 0x10 && addr[0] != 0x28) {
Serial.print("Device is not recognized");
return -1000;
}

ds.reset();
ds.select(addr);
ds.write(0x44,1); // start conversion, with parasite power on at the end

byte present = ds.reset();
ds.select(addr);
ds.write(0xBE); // Read Scratchpad


for (int i = 0; i < 9; i++) { // we need 9 bytes
data[i] = ds.read();
}

ds.reset_search();

byte MSB = data[1];
byte LSB = data[0];

float tempRead = ((MSB << 8) | LSB); //using two's compliment
float TemperatureSum = tempRead / 16;

return TemperatureSum;

}

float Humidity()
{
 int H = analogRead(HumPin);
 float HV = H * BitToVolt;
 RH = (400 * ((125 * HV) - 66) ) / 1023;
 
 return RH;
} 

float DewPoint()
{
  float temperature = getTemp();
  float RH = Humidity();
  float beta = 17.62;
  float lambda = 243.12;
 
 //float H = ((log(RH) - 2) / 0.4343) + ((beta * temperature) / (lambda + temperature));
 //float result = (lambda * H) / (beta - H);
 
 float H1 = lambda * (log(RH/100) + ((beta * temperature) / (lambda + temperature)));
 float H2 = beta - (log(RH/100) + ((beta * temperature) / (lambda + temperature)));
 float delta = H1/H2;
 
 return delta;
}

float BattV()
{
 int V = analogRead(BattPin);
 float Volt = V * BitToVolt * 2.2;
 return Volt;
}
 
 
// Setup and Loop.

void setup(){
  pinMode(RADIO_SPACE_PIN, OUTPUT);
  pinMode(RADIO_MARK_PIN, OUTPUT);
  pinMode(LED_PIN, OUTPUT);
  delay(300);
  sprintf(WAITSTRING, "Starting up, please wait...\n");
  rtty_txstring(WAITSTRING); 
  Serial1.begin(9600);
  Serial2.begin(9600);
  
  delay(5000);
  
  Wire.begin();
  bmp085Calibration();
  
  setupGPS();
  delay(100);
  
  analogReference(INTERNAL2V56);
  sprintf(STARTSTRING, "OERNEN-II Powerup Completed.\n");
  rtty_txstring(STARTSTRING);
  Serial2.println(STARTSTRING);
}

void loop()
{
  char checksum[10];
  int n;
  
  gps_check_nav();
  gps_check_lock();
  gps_get_position();
  gps_get_time();
  error = GPSerrorM + GPSerrorL + GPSerrorP + GPSerrorT;
  float temperature = bmp085GetTemperature(bmp085ReadUT()); //MUST be called first
  float pressure = bmp085GetPressure(bmp085ReadUP());
  float atm = pressure / 101325; // "standard atmosphere"
  float altitude = calcAltitude(pressure); //Uncompensated caculation - in Meters 
  float hum = Humidity();
  float delta = DewPoint();
  float volt = BattV();
  float temperature_DS = getTemp();
  
  fmtDouble(temperature, 2, TemperatureString);
  fmtDouble(pressure, 2, PressureString);
  fmtDouble(altitude, 2, AltitudeString);
  fmtDouble(temperature_DS, 2, DSTemperString);
  fmtDouble(hum, 2, HumidityString);
  fmtDouble(delta, 2, DewPointString);
  fmtDouble(volt, 2, VoltageString);
  
  sprintf(DATASTRING, "$$OERNEN-II,%d,%02d:%02d:%02d,%s,%s,%s,%s,%s,%s,%s,%s,%s", count, hour, minute, second, latitude, longitude, TemperatureString, PressureString, AltitudeString, DSTemperString, HumidityString, DewPointString, VoltageString);
  /* Append the checksum, skipping the $$ prefix */
   crccat(DATASTRING + 2);
  noInterrupts();
  rtty_txstring(DATASTRING);
  interrupts();
  Serial2.println(DATASTRING);
  count++;
  delay(2000);
}
