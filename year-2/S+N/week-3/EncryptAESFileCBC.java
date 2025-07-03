import java.security.Key;
import javax.crypto.*;
import javax.crypto.spec.SecretKeySpec;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.RandomAccessFile;
import javax.crypto.spec.IvParameterSpec;
import java.security.SecureRandom;


public class EncryptAESFileCBC {
      
    static String hexKey="3eafda76cb8b015641cb946708675423";
    static String inFile = "/home/exr/tmp/02_CBC/hello2.txt";
    static String outFile = "/home/exr/tmp/02_CBC/CBCcipherText2";
    
    public static void main(String[] args) {
	try {
	    
	    //Set up the AES key & cipher object
	    SecretKeySpec secretKeySpec = new SecretKeySpec(hexStringToByteArray(hexKey), "AES");
	    Cipher encAEScipher = Cipher.getInstance("AES/CBC/PKCS5Padding");	
	    SecureRandom random = new SecureRandom();
            byte iv[] = new byte[16];
            random.nextBytes(iv);
            IvParameterSpec ivSpec = new IvParameterSpec(iv);
	    encAEScipher.init(Cipher.ENCRYPT_MODE, secretKeySpec,ivSpec);
	    
	    // Open and read the input file
	    RandomAccessFile rawDataFromFile = new RandomAccessFile(inFile, "r");
	    byte[] plainText = new byte[(int) rawDataFromFile.length()];
	    rawDataFromFile.read(plainText);
	    rawDataFromFile.close();
	    
	    //Encrypt the data
	    byte[] cipherText = encAEScipher.doFinal(plainText);
	    
	    //Write file to disk
	    System.out.println("Openning file to write: "+outFile);
	    FileOutputStream outToFile = new FileOutputStream(outFile);
	    outToFile.write(iv);
	    outToFile.write(cipherText);
	    outToFile.close();
	    System.out.println(inFile+" encrypted as "+outFile);
	    
	    
	} catch (Exception e){
	    System.out.println("doh "+e);
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
