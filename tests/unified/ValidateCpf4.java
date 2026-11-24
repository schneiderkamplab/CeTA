import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import javax.xml.XMLConstants;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.SchemaFactory;

/** Streaming batch schema validation, including proofs deeper than libxml2's cap. */
public final class ValidateCpf4 {
    public static void main(String[] args) throws Exception {
        System.setProperty("jdk.xml.maxElementDepth", "0");
        var factory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
        factory.setFeature(XMLConstants.FEATURE_SECURE_PROCESSING, false);
        factory.setProperty(XMLConstants.ACCESS_EXTERNAL_DTD, "");
        factory.setProperty(XMLConstants.ACCESS_EXTERNAL_SCHEMA, "file");
        var schema = factory.newSchema(new File(args[0]));
        var input = new BufferedReader(new InputStreamReader(System.in));
        boolean failed = false;
        for (String path; (path = input.readLine()) != null;) {
            try {
                schema.newValidator().validate(new StreamSource(new File(path)));
                System.out.println("OK\t" + path);
            } catch (Exception e) {
                failed = true;
                System.out.println("ERROR\t" + path + "\t" + e.getMessage().replace('\n', ' '));
            }
        }
        if (failed) System.exit(1);
    }
}
