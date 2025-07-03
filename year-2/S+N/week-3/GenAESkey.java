import java.security.Key;
import javax.crypto.*;
import javax.crypto.spec.SecretKeySpec;
import java.util.Arrays;

public class GenAESkey {

   public static void main(String[] args) {
       try {
	   // Generate a new AES key
	   KeyGenerator sGen = KeyGenerator.getInstance("AES");
	   Key aesKey = sGen.generateKey();
	   byte[] keyBytes = aesKey.getEncoded();

	   System.out.println("Key as bytes: "+(new String(keyBytes)));
	   System.out.println("Key as ints: "+Arrays.toString(keyBytes));
      
	   String printableKey = byteArrayToHexString(keyBytes);
	   System.out.println("Key as hex: "+printableKey);
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

}