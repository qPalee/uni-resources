import java.security.Key;
import javax.crypto.*;
import javax.crypto.spec.SecretKeySpec;
public class EncryptAES {

   static String plainText = "Hello World";
   static String hexKey="3eafda76cb8b015641cb946708675423";
  
   public static void main(String[] args) {
       try {
	 
	   //Create the Key Object
	   Key aesKey = new SecretKeySpec(hexStringToByteArray(hexKey), "AES");
	 
	   //Initiate the cipher object for encryption
	   Cipher encAEScipher = Cipher.getInstance("AES");
	   encAEScipher.init(Cipher.ENCRYPT_MODE, aesKey);
	   
	   // Encrypt the plain text
	   byte[] cipherText = encAEScipher.doFinal(plainText.getBytes());
	   
	   // Ciphertext as hex.
	   String printablecipherText = byteArrayToHexString(cipherText);
	   System.out.println("Cipher text: "+printablecipherText);

       } catch (Exception e){
	   System.out.println("doh");
       } 
   }
    
    private static String byteArrayToHexString(byte[] data) {
	StringBuffer buf = new StringBuffer();
	for (int i = 0; i < data.length; i++) {
	    int halfbyte = (data[i] >>> 4) & 0x0F;
	    int two_halfs = 0;
	    do {
		if ((0 <= halfbyte) && (halfbyte <= 9))
		    buf.append((char) ('0' + halfbyte));
		else
		    buf.append((char) ('a' + (halfbyte - 10)));
		halfbyte = data[i] & 0x0F;
	    } while(two_halfs++ < 1);
	}
	return buf.toString();
    }
 
   private static byte[] hexStringToByteArray(String s) {
	int len = s.length();
	byte[] data = new byte[len / 2];
	for (int i = 0; i < len; i += 2) {
	    data[i / 2] = (byte) ((Character.digit(s.charAt(i), 16) << 4)
				  + Character.digit(s.charAt(i+1), 16));
	}
        return data;
    }
    
}