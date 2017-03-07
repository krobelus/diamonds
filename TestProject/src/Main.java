import java.util.List;
import java.util.LinkedList;
import java.util.Collection;

public class Main {

	public static void main(String[] args) {
		List list = new LinkedList();
                Guitar guitar = new Guitar();
                Ocarina ocarina = new Ocarina();
		list.add(guitar);
		list.add(ocarina);

                Collection col = new LinkedList();
                col.add((Instrument) ocarina);
	}
}
